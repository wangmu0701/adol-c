/*----------------------------------------------------------------------------
 ADOL-C -- Automatic Differentiation by Overloading in C++
 File:     hess_rev.cpp

 Contents: The second order reverse mode for Hessian.

 Routines: 
    // For dense Hessian evaluation 
    int hessian_dense(short, int, double*, double**);

    // For sparse Hessian evaluation
    int hessian_sparse(short, int, double*, int*,
                       unsigned int**, unsigned int**, double**);

 This file implements the second order reverse mode described in the paper :
    Wang, Mu, Assefaw Gebremedhin, and Alex Pothen. "Capitalizing on live
    variables: new algorithms for efficient Hessian computation via auto-
    matic differentiation." Mathematical Programming Computation 8.4 (20-
    16): 393-433.

 The following features of ADOL-C are not supported in this routine (for now)
   1 : The advanced branching options
   2 : The advector operators
   3 : The Adjoinable MPI operations

 CAUTION : Please don't reuse any active independent variables, and declare
           all independent variables all together. This should be a general
           rule. For example, the following coding style will cause errors.
              xad[0] << x[0];
              xad[1] = xad[0];
              xad[0] << x[1];

----------------------------------------------------------------------------*/
#include <adolc/interfaces.h>
#include <adolc/adalloc.h>
#include "oplate.h"
#include "taping_p.h"
#include <adolc/convolut.h>
#include "dvlparms.h"
#include <adolc/hess_rev.h>
#include <iostream>
#include <limits>
#include <vector>
#include <map>

#include <math.h>

static const locint NULL_LOC = std::numeric_limits<locint>::max();

class DerivativeInfo {
 public:
  DerivativeInfo() {
    clear();
  }

  void clear() {
    r = NULL_LOC; x = NULL_LOC; y = NULL_LOC;
    dx = 0.0; dy = 0.0;
    pxx = 0.0; pxy = 0.0; pyy = 0.0;
  }
  unsigned char opcode;
  locint r, x, y;
  double dx, dy;
  double pxx, pxy, pyy;
};

class AbstractHessian {
 public:
  AbstractHessian() = default;
  virtual void init(locint size) = 0;
  virtual ~AbstractHessian() = default;
  virtual void increase(locint x, locint y, double w) = 0;
  virtual void increase_d(locint x, double w) = 0;
  virtual void get_row(locint v, locint*, double* r) = 0;
 protected:
  locint _size;
};

class DenseHessian : public AbstractHessian {
 public:
  DenseHessian() = default;
  ~DenseHessian() {
    myfree2(_H);
  }
  void init(locint size) {
    this->_size = size; 
    _H = myalloc2(size, size);
    for (locint i = 0; i < _size; i++) {
      for (locint j = 0; j < _size; j++) {
        _H[i][j] = 0;
      }
    }
  }
  void increase(locint x, locint y, double w) {
    _H[x][y] += w;
    _H[y][x] += w;
  }
  void increase_d(locint x, double w) {
    _H[x][x] += w;
  } 
  double get_val(locint x, locint y) const {
    return _H[x][y];
  }
  void get_row(locint v, locint* rp, double* rw) {
    int count = 0;
    for (locint i = 0; i < _size; i++) {
      if (_H[v][i] != 0) {
        rp[count] = i;
        rw[count] = _H[v][i];
        count++;
      }
      _H[v][i] = _H[i][v] = 0;
    }
    rp[count] = NULL_LOC;
  }
 private:
  double** _H;
};


class SparseHessian : public AbstractHessian {
 public:
  SparseHessian() = default;
  ~SparseHessian() = default;
  void init(locint size) {
    this->_size = _size;
  }

  void increase(locint x, locint y, double w) {
    _H[x][y] += w;
    _H[y][x] += w;
  }
  void increase_d(locint x, double w) {
    _H[x][x] += w;
  }
  void get_row(locint v, locint* rp, double* rw) {
    int count = 0;
    if (_H.find(v) != _H.end()) {
      auto row = _H.find(v)->second;
      auto iter = row.begin();
      while (iter != row.end()) {
        rp[count] = iter->first;
        rw[count] = iter->second;
        if (rp[count] != v) {
          _H.find(rp[count])->second.erase(v);
        }
        ++iter;
        count++;
      } 
    }
    _H.erase(v);
    rp[count] = NULL_LOC;
  }
  void get_coo_format(int indep,
                      int* nnz, 
                      unsigned int **rind,
                      unsigned int **cind,
                      double ** values,
                      locint* indexmap,
                      std::map<locint, locint>& inv_indexmap) {
    int count = 0;
    auto iter1 = _H.cbegin();
    while (iter1 != _H.cend()) {
      auto iter2 = iter1->second.cbegin();
      while (iter2 != iter1->second.cend()) {
        if (iter1->first <= iter2->first &&
            inv_indexmap.find(iter1->first) != inv_indexmap.end() &&
            inv_indexmap.find(iter2->first) != inv_indexmap.end()) {
          count++;
        }
        ++iter2;
      }
      ++iter1;
    }
    (*nnz) = count;
    (*rind) = (unsigned int*)malloc(sizeof(unsigned int) * count);
    (*cind) = (unsigned int*)malloc(sizeof(unsigned int) * count);
    (*values) = (double*)malloc(sizeof(double) * count);
    count = 0;
    for (locint i = 0; i < indep; i++) {
      if (_H.find(indexmap[i]) != _H.end()) {
        auto row = _H.find(indexmap[i])->second;
        auto iter = row.cbegin();
        while (iter != row.cend()) {
          if (i >= inv_indexmap[iter->first]) {
            (*rind)[count] = i;
            (*cind)[count] = inv_indexmap[iter->first];
            (*values)[count] = iter->second;
            count++;
          }
          ++iter;
        }
      }
    }
  }
 private:
  std::map<locint, std::map<locint, double>> _H;
};

static void branch_switch_warning(const char* opname) {
  fprintf(DIAG_OUT, "ADOL-C Error: Branch switch detected in comparison (%s).\n, Forward sweep aborted! Retaping required!\n", opname);
}

static void unsupported_op_warning(const char* opname, unsigned char opcode) {
  fprintf(DIAG_OUT, "ADOL-C Error: Unsupported %s operator (%d) in second order reverse mode.\n", opname, opcode);
}

// A forward mode reevaluation for the intermediate values
static int reevaluate(short tnum,
                const double * const basepoint,
                int max_live,
                std::vector<double>& values) {
    double* dp_T0 = myalloc1(max_live);
    int ret_c = 3;
    init_for_sweep(tnum);
    unsigned char opcode;
    locint size = 0;
    locint res  = 0;
    locint arg  = 0;
    locint arg1 = 0;
    locint arg2 = 0;
    double coval;
    double* d;    
    int indexi = 0;

    opcode = get_op_f();
    while (opcode != end_of_tape) {
        switch (opcode) {
            case end_of_op:                                    /* end_of_op */
                get_op_block_f();
                opcode=get_op_f();
                /* Skip next operation, it's another end_of_op */
                break;
            case end_of_int:                                  /* end_of_int */
                get_loc_block_f();
                break;
            case end_of_val:                                  /* end_of_val */
                get_val_block_f();
                break;
            case start_of_tape:                            /* start_of_tape */
                break;
            case end_of_tape:                                /* end_of_tape */
                break;

            case eq_zero  :                                      /* eq_zero */
                arg  = get_locint_f();
                if (dp_T0[arg] != 0) {
                  branch_switch_warning("eq_zero");
                  ret_c = -1;
                  opcode = end_of_tape;
                  continue;
                }
                break;
            case neq_zero :                                     /* neq_zero */
                arg  = get_locint_f();
                if (dp_T0[arg] == 0) {
                  branch_switch_warning("neq_zero");
                  ret_c = -1;
                  opcode = end_of_tape;
                  continue;
                }
                break;
            case le_zero  :                                      /* le_zero */
                arg  = get_locint_f();
                if (dp_T0[arg] > 0) {
                  branch_switch_warning("le_zero");
                  ret_c = -1;
                  opcode = end_of_tape;
                  continue;
                }
                break;
            case gt_zero  :                                      /* gt_zero */
                arg  = get_locint_f();
                if (dp_T0[arg] <= 0) {
                  branch_switch_warning("gt_zero");
                  ret_c = -1;
                  opcode = end_of_tape;
                  continue;
                }
                break;
            case ge_zero  :                                      /* ge_zero */
                arg  = get_locint_f();
                if (dp_T0[arg] < 0) {
                  branch_switch_warning("ge_zero");
                  ret_c = -1;
                  opcode = end_of_tape;
                  continue;
                }
                break;
            case lt_zero  :                                      /* lt_zero */
                arg  = get_locint_f();
                if (dp_T0[arg] >= 0) {
                  branch_switch_warning("lt_zero");
                  ret_c = -1;
                  opcode = end_of_tape;
                  continue;
                }
                break;
            case assign_a:     /* assign an adouble variable an    assign_a */
                /* adouble value. (=) */
                arg = get_locint_f();
                res = get_locint_f();
                dp_T0[res]= dp_T0[arg];
                break;
            case neg_sign_p:
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg];
                dp_T0[res] = -coval;
                break;
            case recipr_p:
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg];
                dp_T0[res] = 1.0 / coval;
                break;
            case assign_p:
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg];
                dp_T0[res] = coval;
                break;
            case assign_d:      /* assign an adouble variable a    assign_d */
                /* double value. (=) */
                res  = get_locint_f();
                coval=get_val_f();
                dp_T0[res]= coval;
                break;
            case assign_d_one:/* assign an adouble variable a  assign_d_one */
                /* double value. (1) (=) */
                res  = get_locint_f();
                dp_T0[res]= 1.0;
                break;
            case assign_d_zero:/* assign an adouble variable  assign_d_zero */
                /* double value. (0) (=) */
                res  = get_locint_f();
                dp_T0[res]= 0.0;
                break;
            case assign_ind: /* assign an adouble variable an    assign_ind */
                /* independent double value (<<=) */
                res  = get_locint_f();
                dp_T0[res]= basepoint[indexi++];
                break;
            case assign_dep:     /* assign a float variable a    assign_dep */
                /* dependent adouble value. (>>=) */
                res = get_locint_f();
                break;

            case eq_plus_d:      /* Add a floating point to an    eq_plus_d */
                /* adouble. (+=) */
                res   = get_locint_f();
                coval = get_val_f();
                dp_T0[res] += coval;
                break;
            case eq_plus_p:
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg];
                dp_T0[res] += coval;
                break;
            case eq_plus_a:       /* Add an adouble to another    eq_plus_a */
                /* adouble. (+=) */
                arg  = get_locint_f();
                res  = get_locint_f();
                dp_T0[res]+= dp_T0[arg];
                break;
            case eq_plus_prod:    /* Add an product to an      eq_plus_prod */
                /* adouble. (+= x1*x2) */
                arg1 = get_locint_f();
                arg2 = get_locint_f();
                res  = get_locint_f();
                values.push_back(dp_T0[arg1]);
                values.push_back(dp_T0[arg2]);
                dp_T0[res] += dp_T0[arg1]*dp_T0[arg2];
                break;
            case eq_min_d: /* Subtract a floating point from an    eq_min_d */
                /* adouble. (-=) */
                res   = get_locint_f();
                coval = get_val_f();
                dp_T0[res] -= coval;
                break;
            case eq_min_p:
                /* adouble. (-=) */
                arg = get_locint_f();
                res = get_locint_f();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg];
                dp_T0[res] -= coval;
                break;
            case eq_min_a:  /* Subtract an adouble from another    eq_min_a */
                /* adouble. (-=) */
                arg  = get_locint_f();
                res  = get_locint_f();
                dp_T0[res]-= dp_T0[arg];
                break;
            case eq_min_prod: /* Subtract an product from an    eq_min_prod */
                /* adouble. (-= x1*x2) */
                arg1 = get_locint_f();
                arg2 = get_locint_f();
                res  = get_locint_f();
                values.push_back(dp_T0[arg1]);
                values.push_back(dp_T0[arg2]);
                dp_T0[res] -= dp_T0[arg1]*dp_T0[arg2];
                break;
            case eq_mult_d:       /* Multiply an adouble by a     eq_mult_d */
                res   = get_locint_f();
                coval = get_val_f();
                dp_T0[res] *= coval;
                break;
            case eq_mult_a:   /* Multiply one adouble by another  eq_mult_a */
                /* (*=) */
                arg  = get_locint_f();
                res  = get_locint_f();
                values.push_back(dp_T0[res]);
                values.push_back(dp_T0[arg]);
                dp_T0[res]*= dp_T0[arg];
                break;
            case eq_mult_p:
                /* adouble. (*=) */
                arg = get_locint_f();
                res = get_locint_f();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg];
                dp_T0[res] *= coval;
                break;
            case incr_a:                  /* Increment an adouble    incr_a */
                res = get_locint_f();
                dp_T0[res]++;
                break;
            case decr_a:                  /* Increment an adouble    decr_a */
                res = get_locint_f();
                dp_T0[res]--;
                break;

            case plus_a_a:           /* : Add two adoubles. (+)    plus a_a */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                dp_T0[res]=dp_T0[arg1]+dp_T0[arg2];
                break;
            case plus_d_a:       /* Add an adouble and a double    plus_d_a */
                /* (+) */
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                dp_T0[res]= dp_T0[arg] + coval;
                break;
            case plus_a_p:
                arg   = get_locint_f();
                arg1  = get_locint_f();
                res   = get_locint_f();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg1];
                dp_T0[res] = dp_T0[arg] + coval;
                break;
            case min_a_a:        /* Subtraction of two adoubles     min_a_a */
                /* (-) */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                dp_T0[res]=dp_T0[arg1]-dp_T0[arg2];
                break;
            case min_d_a:          /* Subtract an adouble from a    min_d_a */
                /* double (-) */
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                dp_T0[res]  = coval - dp_T0[arg];
                break;
            case min_a_p:
                arg   = get_locint_f();
                arg1  = get_locint_f();
                res   = get_locint_f();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg1];
                dp_T0[res] = dp_T0[arg] - coval;
                break;
            case mult_a_a:         /* Multiply two adoubles (*)    mult_a_a */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                values.push_back(dp_T0[arg1]);
                values.push_back(dp_T0[arg2]);
                dp_T0[res]=dp_T0[arg1]*dp_T0[arg2];
                break;
            case mult_d_a:   /* Multiply an adouble by a double    mult_d_a */
                /* (*) */
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                dp_T0[res]  = coval * dp_T0[arg];
                break;
            case mult_a_p:   /* Multiply an adouble by a double    mult_a_p */
                /* (*) */
                arg   = get_locint_f();
                arg1  = get_locint_f();
                res   = get_locint_f();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg1];
                dp_T0[res] = dp_T0[arg] * coval;
                break;
            case div_a_a:     /* Divide an adouble by an adouble    div_a_a */
                /* (/) */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                values.push_back(dp_T0[arg1]);
                values.push_back(dp_T0[arg2]);
                dp_T0[res]=dp_T0[arg1]/dp_T0[arg2];
                break;
            case div_d_a:       /* Division double - adouble (/)    div_d_a */
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                values.push_back(dp_T0[arg]);
                dp_T0[res]  = coval / dp_T0[arg];
                break;
            case div_p_a:       /* Division double - adouble (/)    div_p_a */
                arg   = get_locint_f();
                arg1  = get_locint_f();
                res   = get_locint_f();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg1];
                values.push_back(dp_T0[arg]);
                dp_T0[res] = coval / dp_T0[arg];
                break;
            case pos_sign_a:                                  /* pos_sign_a */
                arg  = get_locint_f();
                res  = get_locint_f();
                dp_T0[res]= dp_T0[arg];
                break;
            case neg_sign_a:                                  /* neg_sign_a */
                arg  = get_locint_f();
                res  = get_locint_f();
                dp_T0[res]= -dp_T0[arg];
                break;

            case exp_op:                    /* exponent operation    exp_op */
                arg  = get_locint_f();
                res  = get_locint_f();
                values.push_back(dp_T0[arg]);
                dp_T0[res]= exp(dp_T0[arg]);
                break;
            case log_op:                                         /* log_op */
                arg  = get_locint_f();
                res  = get_locint_f();
                values.push_back(dp_T0[arg]);
                dp_T0[res]= log(dp_T0[arg]);
                break;
            case pow_op:                                         /* pow_op */
                arg  = get_locint_f();
                res  = get_locint_f();
                coval   = get_val_f();
                values.push_back(dp_T0[arg]);
                dp_T0[res] = pow(dp_T0[arg], coval);
                break;
            case pow_op_p:                                      /* pow_op_p */ 
                arg   = get_locint_f();
                arg1  = get_locint_f();
                res   = get_locint_f();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg1];
                values.push_back(dp_T0[arg]);
                dp_T0[res] = pow(dp_T0[arg], coval);
                break; 
            case sqrt_op:                                       /* sqrt_op */
                arg  = get_locint_f();
                res  = get_locint_f();
                values.push_back(dp_T0[arg]);
                dp_T0[res]= sqrt(dp_T0[arg]);
                break;
            case sin_op:                       /* sine operation    sin_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                values.push_back(dp_T0[arg1]);
                dp_T0[arg2]= cos(dp_T0[arg1]);
                dp_T0[res] = sin(dp_T0[arg1]);
                break;
            case cos_op:                     /* cosine operation    cos_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                values.push_back(dp_T0[arg1]);
                dp_T0[arg2]= sin(dp_T0[arg1]);
                dp_T0[res] = cos(dp_T0[arg1]);
                break;
            case atan_op:                                       /* atan_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                values.push_back(dp_T0[arg1]);
                dp_T0[res] = atan(dp_T0[arg1]);
                break;
            case asin_op:                                       /* asin_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                values.push_back(dp_T0[arg1]);
                dp_T0[res] = asin(dp_T0[arg1]);
                break;
            case acos_op:                                       /* acos_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                values.push_back(dp_T0[arg1]);
                dp_T0[res] = acos(dp_T0[arg1]);
                break;

#ifdef ATRIG_ERF
            case asinh_op:                                     /* asinh_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                values.push_back(dp_T0[arg1]);
                dp_T0[res] = asinh(dp_T0[arg1]);
                break;
            case acosh_op:                                     /* acosh_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                values.push_back(dp_T0[arg1]);
                dp_T0[res] = acosh(dp_T0[arg1]);
                break;
            case atanh_op:                                     /* atanh_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                values.push_back(dp_T0[arg1]);
                dp_T0[res] = atanh(dp_T0[arg1]);
                break;
            case erf_op:                                         /* erf_op */
                arg1 = get_locint_f();
                arg2 = get_locint_f();
                res  = get_locint_f();
                values.push_back(dp_T0[arg1]);
                dp_T0[res] = erf(dp_T0[arg1]);
                break;
#endif

            case min_op:                                         /* min_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                if (dp_T0[arg1] > dp_T0[arg2]) {
                    values.push_back(1.0);
                    if (coval) {
                        MINDEC(ret_c, 2);
                    }
                    dp_T0[res] = dp_T0[arg2];
                } else {
                    values.push_back(-1.0);
                    if (dp_T0[arg1] < dp_T0[arg2]) {
                        if (!coval) {
                            MINDEC(ret_c, 2);
                        }
                    } else if (arg1 != arg2) {
                        MINDEC(ret_c, 1);
                    }
                    dp_T0[res] = dp_T0[arg1];
                }
                break;
            case abs_val:                                       /* abs_val */
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                values.push_back(dp_T0[arg]);
                if (dp_T0[arg] < 0.0) {
                    if (coval) {
                        MINDEC(ret_c, 2);
                    }
                } else if (dp_T0[arg] > 0.0) {
                    if (!coval) {
                        MINDEC(ret_c, 2);
                    }
                } else {
                    MINDEC(ret_c, 1);
                }
                dp_T0[res]  = fabs(dp_T0[arg]);
                break;
            case ceil_op:          /* Compute ceil of adouble      ceil_op */
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                if (coval != dp_T0[arg]) {
                    MINDEC(ret_c, 2);
                } else {
                    MINDEC(ret_c, 0);
                }
                dp_T0[res]  = ceil(dp_T0[arg]);
                break;
            case floor_op:         /* Compute floor of adouble    floor_op */
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                if (coval != dp_T0[arg]) {
                    MINDEC(ret_c, 2);
                } else {
                    MINDEC(ret_c, 0);
                }
                dp_T0[res]  = floor(dp_T0[arg]);
                break;

            case cond_assign:                               /* cond_assign */
                arg   = get_locint_f();
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                values.push_back(dp_T0[arg]);
                if (dp_T0[arg] > 0){
                    if (coval <= 0){
                        MINDEC(ret_c, 2);
                    }
                    dp_T0[res] = dp_T0[arg1];
                } else {
                    if (coval > 0){
                        MINDEC(ret_c, 2);
                    }
                    if (dp_T0[arg] == 0 && arg1 != arg2) {
                        MINDEC(ret_c, 0);
                    }
                    dp_T0[res] = dp_T0[arg2];
                }
                break;
            case cond_eq_assign:                           /* cond_eq_assign */
                arg   = get_locint_f();
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                values.push_back(dp_T0[arg]);
                if (dp_T0[arg] >= 0){
                    if (coval < 0){
                        MINDEC(ret_c, 2);
                    }
                    if (dp_T0[arg] == 0 && arg1 != arg2) {
                        MINDEC(ret_c, 0);
                    }
                    dp_T0[res] = dp_T0[arg1];
                } else {
                    if (coval >= 0){
                        MINDEC(ret_c, 2);
                    }
                    dp_T0[res] = dp_T0[arg2];
                }
                break;
            case cond_assign_s:                           /* cond_assign_s */
                arg   = get_locint_f();
                arg1  = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                values.push_back(dp_T0[arg]);
                if (dp_T0[arg] > 0) {
                    if (coval <= 0){
                        MINDEC(ret_c, 2);
                    }
                    dp_T0[res] = dp_T0[arg1];
                } else {
                    if (coval > 0) {
                        MINDEC(ret_c, 2);
                    }
                    if (dp_T0[arg] == 0 && arg1 != res) {
                        MINDEC(ret_c, 0);
                    }
                }
                break;
            case cond_eq_assign_s:                     /* cond_eq_assign_s */
                arg   = get_locint_f();
                arg1  = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                values.push_back(dp_T0[arg]);
                if (dp_T0[arg] >= 0) {
                    if (coval < 0){
                        MINDEC(ret_c, 2);
                    }
                    if (dp_T0[arg] == 0 && arg1 != res) {
                        MINDEC(ret_c, 0);
                    }
                    dp_T0[res] = dp_T0[arg1];
                } else {
                    if (coval >= 0) {
                        MINDEC(ret_c, 2);
                    }
                }
                break;
            case take_stock_op:                            /* take_stock_op */
                size = get_locint_f();
                res  = get_locint_f();
                d    = get_val_v_f(size);
                for (int i = 0; i < size; i++) {
                    dp_T0[res+i] = d[i];
                }
                break;
            case death_not:                                    /* death_not */
                arg1 = get_locint_f();
                arg2 = get_locint_f();
                break;
            case gen_quad:
                unsupported_op_warning("gen_quad", opcode);
                ret_c = -2;
                opcode = end_of_tape;
                continue;
            case neq_a_a:
            case eq_a_a:
            case le_a_a:
            case ge_a_a:
            case lt_a_a:
            case gt_a_a:
            case neq_a_p:
            case eq_a_p:
            case le_a_p:
            case ge_a_p:
            case lt_a_p:
            case gt_a_p:            
                unsupported_op_warning("ADVANCED_BRANCHING", opcode);
                ret_c = -2;
                opcode = end_of_tape;
                continue;
            case subscript:
            case subscript_ref:
            case ref_copyout:
            case ref_incr_a:
            case ref_decr_a:
            case ref_assign_d:
            case ref_assign_p:
            case ref_assign_d_zero:
            case ref_assign_d_one:
            case ref_assign_a:
            case ref_assign_ind:
            case ref_eq_plus_d:
            case ref_eq_plus_p:
            case ref_eq_plus_a:
            case ref_eq_min_d:
            case ref_eq_min_p:
            case ref_eq_min_a:
            case ref_eq_mult_d:
            case ref_eq_mult_p:
            case ref_eq_mult_a:
            case vec_copy:
            case vec_dot:
            case vec_axpy:
            case ref_cond_assign:
            case ref_cond_eq_assign:
            case ref_cond_assign_s:
            case ref_cond_eq_assign_s:
                unsupported_op_warning("ADVECTOR_OPERATORS", opcode);
                ret_c = -2;
                opcode = end_of_tape;
                continue;
            case ext_diff:
                unsupported_op_warning("ext_diff", opcode);
                ret_c = -2;
                opcode = end_of_tape;
                continue;
            case ext_diff_iArr:
                unsupported_op_warning("ext_diff_iArr", opcode);
                ret_c = -2;
                opcode = end_of_tape;
                continue;
            case ext_diff_v2:
                unsupported_op_warning("ext_diff_v2", opcode);
                ret_c = -2;
                opcode = end_of_tape;
                continue;
            case ampi_send:
            case ampi_recv:
            case ampi_isend:
            case ampi_irecv:
            case ampi_wait:
            case ampi_barrier:
            case ampi_gather:
            case ampi_scatter:
            case ampi_allgather:
            case ampi_gatherv:
            case ampi_scatterv:
            case ampi_allgatherv:
            case ampi_bcast:
            case ampi_reduce:
            case ampi_allreduce:
                unsupported_op_warning("ADJOINTABLE_MPI", opcode);
                ret_c = -2;
                opcode = end_of_tape;
                continue;
            default:
                unsupported_op_warning("unknown", opcode);
                ret_c = -2;
                opcode = end_of_tape;
                continue;
        }  // end switch
        opcode = get_op_f();
    } // end while
    end_sweep();
    myfree1(dp_T0);
    return ret_c;
}


static void accumulate_derivative(DerivativeInfo& info,
                                  AbstractHessian* H,
                                  double* adjoint,
                                  locint* rp,
                                  double* rw) {
    if (info.r != NULL_LOC) {
        // Step 0: pseudo binary function
        if (info.x != NULL_LOC && info.x == info.y) {
            info.dx += info.dy; info.dy = 0;
            info.pxx += info.pyy + 2.0 * info.pxy;
            info.pyy = info.pxy = 0;
            info.y = NULL_LOC;
        }
        // Step 1: retrieve w and r
        double w = adjoint[info.r]; adjoint[info.r] = 0.0;
        H->get_row(info.r, rp, rw);
/*

        for (int i = 0; i < max_live; i++) {
            r[i] = H[info.r][i];
            H[info.r][i] = 0; H[i][info.r] = 0;
        }
*/
        // Step 2: accumulate adjoints
        if (info.x != NULL_LOC) {
            adjoint[info.x] += info.dx * w;
        }
        if (info.y != NULL_LOC) {
            adjoint[info.y] += info.dy * w;
        }
        // Step 3: accumulate Hessian
        locint p;
        double pw = 0.0;
        int l = 0;
        while (rp[l] != NULL_LOC) {
            p = rp[l];
            pw = rw[l];
            if (pw != 0) {
                if (info.y != NULL_LOC) {
                    if (info.r != p) {
                        if (info.x == p) {
                            H->increase_d(p, 2*info.dx*pw);
                        } else {
                            H->increase(info.x, p, info.dx*pw);
                        }
                        if (info.y == p) {
                            H->increase_d(p, 2*info.dy*pw);
                        } else {
                            H->increase(info.y, p, info.dy*pw);
                        }
                    } else { // info.r == p, self edge
                        H->increase_d(info.x, info.dx*info.dx*pw);
                        H->increase_d(info.y, info.dy*info.dy*pw);
                        H->increase(info.x, info.y, info.dx*info.dy*pw);
                    }
                } else if (info.x != NULL_LOC) {
                    if (info.r != p) {
                        if (info.x == p) {
                            H->increase_d(p, 2*info.dx*pw);
                        } else {
                            H->increase(info.x, p, info.dx*pw);
                        }
                    } else {
                        H->increase_d(info.x, info.dx*info.dx*pw);
                    }
                }
            } // end pw != 0.0
            l++;
        } // end for
        if (w != 0) {
            if (info.pxx != 0.0) {
                H->increase_d(info.x, info.pxx * w);
            }
            if (info.pyy != 0.0) {
                H->increase_d(info.y, info.pyy * w);
            }
            if (info.pxy != 0.0) {
                H->increase(info.x, info.y, info.pxy * w);
            }
        }
    } // end info.r != NULL_LOC
}
// Evaluating Dense Hessian using Second order reverse mode

static int second_order_rev(short tnum,  // tape id
                            int indep,   // # of indeps
                            double * basepoint,
                            AbstractHessian * H,
                            locint* indexmap,
                            std::map<locint, locint>& inv_indexmap)
{
    init_rev_sweep(tnum);
    if ( (1 != ADOLC_CURRENT_TAPE_INFOS.stats[NUM_DEPENDENTS]) ||
            (indep != ADOLC_CURRENT_TAPE_INFOS.stats[NUM_INDEPENDENTS]) )
        fail(ADOLC_REVERSE_COUNTS_MISMATCH);
    int indexi = ADOLC_CURRENT_TAPE_INFOS.stats[NUM_INDEPENDENTS];
    int max_live = ADOLC_CURRENT_TAPE_INFOS.stats[NUM_MAX_LIVES] + 1;
    end_sweep();

    std::vector<double> values;
    int ret_c = reevaluate(tnum, basepoint, max_live, values);   
    if (ret_c < 0) { // something wrong when reevaluate, do nothing
      return ret_c;
    }

    H->init(max_live);
    double* adjoint = myalloc1(max_live);
    double w;
    locint* rp = (locint*)malloc(sizeof(locint) * max_live);
    double* rw = myalloc1(max_live);

    for (int i = 0; i < max_live; i++) {
        adjoint[i] = 0;
    }
    auto rit = values.crbegin();

    unsigned char opcode;
    locint size = 0;
    locint res  = 0;
    locint arg  = 0;
    locint arg1 = 0;
    locint arg2 = 0;
    double coval = 0;
    double vx, vy;

    DerivativeInfo info;

    bool done = false;
    init_rev_sweep(tnum);
    opcode = get_op_r();    
    while (opcode != start_of_tape) {
      info.clear();
      info.opcode = opcode;

      // Ignore what was BEFORE the declarition of first independent variable
      if (!done) {
        /* Switch statement to execute the operations in Reverse */
        switch (opcode) {

                /************************************************************/
                /*                                                  MARKERS */
                /*----------------------------------------------------------*/
            case end_of_op:                                    /* end_of_op */
                get_op_block_r();
                opcode = get_op_r();
                /* Skip next operation, it's another end_of_op */
                break;
            case end_of_int:                                  /* end_of_int */
                get_loc_block_r(); /* Get the next int block */
                break;
            case end_of_val:                                  /* end_of_val */
                get_val_block_r(); /* Get the next val block */
                break;
            case start_of_tape:                            /* start_of_tape */
                break;
            case end_of_tape:                                /* end_of_tape */
                discard_params_r();
                break;

                /************************************************************/
                /*                                               COMPARISON */
                /*----------------------------------------------------------*/
            case eq_zero  :                                      /* eq_zero */
            case neq_zero :                                     /* neq_zero */
            case gt_zero  :                                      /* gt_zero */
            case lt_zero :                                       /* lt_zero */
            case ge_zero :                                       /* ge_zero */
            case le_zero :                                       /* le_zero */
                arg   = get_locint_r();
                break;

                /************************************************************/
                /*                                              ASSIGNMENTS */
                /*----------------------------------------------------------*/
            case assign_a:     /* assign an adouble variable an    assign_a */
                /* adouble value. (=) */
                res = get_locint_r();
                arg = get_locint_r();
                info.r = res;
                info.x = arg;
                info.dx = 1.0;
                break;
            case assign_d:      /* assign an adouble variable a    assign_d */
                /* double value. (=) */
                res   = get_locint_r();
                coval = get_val_r();
                break;

            case neg_sign_p:
            case recipr_p:
            case assign_p:
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg];
                info.r = res;
                break;

            case assign_d_zero: /* assign an adouble a        assign_d_zero */
            case assign_d_one:  /* double value. (=)           assign_d_one */
                res   = get_locint_r();
                info.r = res;
                break;
            case assign_ind: /* assign an adouble variable an    assign_ind */
                /* independent double value (<<=) */
                res = get_locint_r();
                indexi--;
                indexmap[indexi] = res;
                inv_indexmap[res] = indexi;
                if (indexi == 0) {
                  done = true;
                }
                break;
            case assign_dep:     /* assign a float variable a    assign_dep */
                /* dependent adouble value. (>>=) */
                res = get_locint_r();
                adjoint[res] = 1.0;
            break;

                /************************************************************/
                /*                                  OPERATION + ASSIGNMENTS */
                /*----------------------------------------------------------*/
            case eq_plus_d:      /* Add a floating point to an    eq_plus_d */
                /* adouble. (+=) */
                res   = get_locint_r();
                coval = get_val_r();
                break;
            case eq_plus_p:
                /* adouble. (+=) */
                res = get_locint_r();
                arg = get_locint_r();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg];
                break;
            case eq_plus_a:       /* Add an adouble to another    eq_plus_a */
                /* adouble. (+=) */
                res = get_locint_r();
                arg = get_locint_r();
                info.r = res;
                info.x = res;
                info.y = arg;
                info.dx = 1.0; info.dy = 1.0;
                break;
            case eq_min_d: /* Subtract a floating point from an    eq_min_d */
                /* adouble. (-=) */
                res   = get_locint_r();
                coval = get_val_r();
                break;
            case eq_min_p:  /*  Subtract a floating point from an  eq_min_p */
                /* adouble. (-=) */
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg];
                break;
            case eq_min_a:  /* Subtract an adouble from another    eq_min_a */
                /* adouble. (-=) */
                res = get_locint_r();
                arg = get_locint_r();
                info.r = res;
                info.x = res;
                info.y = arg;
                info.dx = 1.0; info.dy = -1.0;
                break;
            case eq_mult_d:        /* Multiply an adouble by a    eq_mult_d */
                /* flaoting point. (*=) */
                res   = get_locint_r();
                coval = get_val_r();
                info.r = res;
                info.x = res;
                info.dx = coval;
                break;
            case eq_mult_p:      /* Multiply an adouble by a    eq_mult_p */
                /* flaoting point. (*=) */
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg];
                info.r = res;
                info.x = res;
                info.dx = coval;
                break;
            case eq_mult_a: /* Multiply one adouble by another    eq_mult_a */
                /* (*=) */
                res = get_locint_r();
                arg = get_locint_r();
                info.r = res;
                info.x = res;
                info.y = arg;
                vy = *rit;++rit;
                vx = *rit;++rit;
                info.dx = vy; info.dy = vx;
                info.pxy = 1.0;
                break;
            case incr_a:                  /* Increment an adouble    incr_a */
            case decr_a:                  /* Increment an adouble    decr_a */
                res   = get_locint_r();
                break;
            case plus_a_a:           /* : Add two adoubles. (+)    plus a_a */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                info.r = res;
                info.x = arg1;
                info.y = arg2;
                info.dx = 1.0; info.dy = 1.0;
                break;
            case plus_a_p:       /* Add an adouble and a double    plus_a_p */
                res   = get_locint_r();
                arg1  = get_locint_r();
                arg   = get_locint_r();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg1];
                info.r = res;
                info.x = arg;
                info.dx = 1.0;
                break;
            case plus_d_a:       /* Add an adouble and a double    plus_d_a */
                /* (+) */
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                info.r = res;
                info.x = arg;
                info.dx = 1.0;
                break;
            case min_a_a:         /* Subtraction of two adoubles    min_a_a */
                /* (-) */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                info.r = res;
                info.x = arg1;
                info.y = arg2;
                info.dx = 1.0; info.dy = -1.0;
                break;
            case min_a_p:           /* Subtract an adouble from a    min_a_p */
                res   = get_locint_r();
                arg1  = get_locint_r();
                arg   = get_locint_r();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg1];
                info.r = res;
                info.x = arg;
                info.dx = -1.0;
                break;
            case min_d_a:           /* Subtract an adouble from a    min_d_a */
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                info.r = res;
                info.x = arg;
                info.dx = -1.0;
                break;
            case mult_a_a:         /* Multiply two adoubles (*)    mult_a_a */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vy = *rit;++rit;
                vx = *rit;++rit;
                info.r = res;
                info.x = arg1;
                info.y = arg2;
                info.dx = vy; info.dy = vx;
                info.pxy = 1.0;
                break;
            case eq_plus_prod:   /* increment a product of     eq_plus_prod */
                /* two adoubles (*) */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                info.r = res;
                info.x = res;
                info.y = max_live - 1;
                info.dx = 1.0; info.dy = 1.0;
                accumulate_derivative(info, H, adjoint, rp, rw);
                info.clear();
                info.r = max_live - 1;
                info.x = arg1;
                info.y = arg2;
                vy = *rit;++rit;
                vx = *rit;++rit;
                info.dx = vy; info.dy = vx;
                info.pxy = 1.0;
                break;
            case eq_min_prod:   /* decrement a product of       eq_min_prod */
                /* two adoubles (*) */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                info.r = res;
                info.x = res;
                info.y = max_live - 1;
                info.dx = 1.0; info.dy = -1.0;
                accumulate_derivative(info, H, adjoint, rp, rw);
                info.clear();
                info.r = max_live - 1;
                info.x = arg1;
                info.y = arg2;
                vy = *rit;++rit;
                vx = *rit;++rit;
                info.dx = vy; info.dy = vx;
                info.pxy = 1.0;
                break;
            case mult_d_a:   /* Multiply an adouble by a double    mult_d_a */
                /* (*) */
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                info.r = res;
                info.x = arg;
                info.dx = coval;
                break;
            case mult_a_p: /* Multiply an adouble by a double    mult_a_p */
                res   = get_locint_r();
                arg1  = get_locint_r();
                arg   = get_locint_r();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg1];
                info.r = res;
                info.x = arg;
                info.dx = coval;
                break;
            case div_a_a:     /* Divide an adouble by an adouble    div_a_a */
                /* (/) */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vy = *rit;++rit;
                vx = *rit;++rit;
                info.r = res;
                info.x = arg1;
                info.y = arg2;
                info.dx = 1.0/vy;
                info.dy = -vx/(vy*vy);
                info.pyy = 2.0*vx/(vy*vy*vy);
                info.pxy = -1.0/(vy*vy);
                break;
            case div_d_a:       /* Division double - adouble (/)    div_d_a */
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                info.r = res;
                info.x = arg;
                vx = *rit;++rit;
                info.dx = -coval/(vx*vx);
                info.pxx = 2.0*coval/(vx*vx*vx);
                break;
            case div_p_a:     /* Division double - adouble (/)    div_p_a */
                res   = get_locint_r();
                arg1  = get_locint_r();
                arg   = get_locint_r();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg1];
                info.r = res;
                info.x = arg;
                vx = *rit;++rit;
                info.dx = -coval/(vx*vx);
                info.pxx = 2.0*coval/(vx*vx*vx);
                break;
            case pos_sign_a:                                  /* pos_sign_a */
                res   = get_locint_r();
                arg   = get_locint_r();
                info.r = res;
                info.x = arg;
                info.dx = 1.0;
                break;
            case neg_sign_a:                                  /* neg_sign_a */
                res   = get_locint_r();
                arg   = get_locint_r();
                info.r = res;
                info.x = arg;
                info.dx = -1.0;
                break;

            /****************************************************************/
            /*                                             UNARY OPERATIONS */
            /*--------------------------------------------------------------*/
            case exp_op:                    /* exponent operation    exp_op */
                res = get_locint_r();
                arg = get_locint_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg;
                info.dx = exp(vx);
                info.pxx = info.dx;
                break;
            case log_op:                                          /* log_op */
                res = get_locint_r();
                arg = get_locint_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg;
                info.dx = 1.0/vx;
                info.pxx = -1.0/(vx*vx);
                break;
            case pow_op:                                          /* pow_op */
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg;
                if (vx == 0.0){
                    info.dx = 0.0;
                    info.pxx = 0.0;
                }
                else{
                    info.dx = coval*(pow(vx, coval)/vx);
                    info.pxx = (coval-1.0)*(info.dx/vx);
                }
                break;
            case pow_op_p:                                      /* pow_op_p */
                res   = get_locint_r();
                arg1  = get_locint_r();
                arg   = get_locint_r();
                coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg1];
                vx = *rit;++rit;
                info.r = res;
                info.x = arg;
                if (vx == 0.0){
                    info.dx = 0.0;
                    info.pxx = 0.0;
                }
                else{
                    info.dx = coval*(pow(vx, coval)/vx);
                    info.pxx = (coval-1.0)*(info.dx/vx);
                }
                break;
            case sqrt_op:                                        /* sqrt_op */
                res = get_locint_r();
                arg = get_locint_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg;
                if (vx == 0.0){
                    info.dx = 0.0;
                    info.pxx = 0.0;
                }
                else{
                    info.dx = 0.5/sqrt(vx);
                    info.pxx = -0.5*(info.dx/vx);
                }
                break;


            case sin_op:                        /* sine operation    sin_op */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg1;
                info.dx = cos(vx);
                info.pxx = -sin(vx);
                break;
            case cos_op:                      /* cosine operation    cos_op */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg1;
                info.dx = -sin(vx);
                info.pxx = -cos(vx);
                break;
            case atan_op:                                       /* atan_op  */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg1;
                info.dx = 1.0/(1.0+vx*vx);
                info.pxx = -(2.0*vx)/((1.0+vx*vx)*(1.0+vx*vx));
                break;
            case asin_op:                                       /* asin_op  */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg1;
                info.dx = 1.0/sqrt(1.0-vx*vx);
                info.pxx = vx/((sqrt(1.0-vx*vx))*(1.0-vx*vx));
                break;
            case acos_op:                                       /* acos_op  */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg1;
                info.dx = -1.0/sqrt(1.0-vx*vx);
                info.pxx = -vx/((sqrt(1.0-vx*vx))*(1.0-vx*vx));
                break;
            case asinh_op:                                      /* asinh_op */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg1;
                info.dx = 1.0/sqrt(1.0+vx*vx);
                info.pxx = -vx*info.dx/(1.0+vx*vx);
                break;
            case acosh_op:                                      /* acosh_op */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg1;
                info.dx = 1.0/sqrt(vx*vx-1.0);
                info.pxx = -vx*info.dx/(vx*vx-1.0);
                break;
            case atanh_op:                                      /* atanh_op */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg1;
                info.dx = 1/(1-vx*vx);
                info.pxx = 2.0*vx*info.dx*info.dx;
                break;
            case erf_op:                                        /* erf_op   */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;++rit;
                info.r = res;
                info.x = arg1;
                info.dx = 2.0/sqrt(acos(-1.0))*exp(-vx*vx);
                info.pxx = -2.0*vx*info.dx;
                break;

            case min_op:                                          /* min_op */
                res   = get_locint_r();
                arg2  = get_locint_r();
                arg1  = get_locint_r();
                coval = get_val_r();
                info.r = res;
                info.dx = 1.0;
                if (*rit < 0) {
                   info.x = arg1; 
                } else {
                   info.x = arg2;
                }
                ++rit;
                break;
            case abs_val:                                        /* abs_val */
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                info.r = res;
                info.x = arg;
                if (*rit > 0) {
                    info.dx = 1.0;
                } else {
                    info.dx = -1.0;
                }
                ++rit;
                break;
            case ceil_op:                                        /* ceil_op */
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                info.r = res;
                info.x = arg;
                info.dx = 0.0;
                break;
            case floor_op:                                      /* floor_op */
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                info.r = res;
                info.x = arg;
                info.dx = 0.0;
                break;
            /****************************************************************/
            /*                                                 CONDITIONALS */
            /*--------------------------------------------------------------*/
            case cond_assign:                                /* cond_assign */
                res   = get_locint_r();
                arg2  = get_locint_r();
                arg1  = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                info.r = res;
                info.dx = 1.0;
                if (*rit > 0) {
                    info.x = arg1;
                } else { // <= 0
                    info.x = arg2;
                }
                ++rit;
                break;
            case cond_eq_assign:                          /* cond_eq_assign */
                res   = get_locint_r();
                arg2  = get_locint_r();
                arg1  = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                info.r = res;
                info.dx = 1.0;
                if (*rit >= 0) {
                    info.x = arg1;
                } else { // < 0
                    info.x = arg2;
                }
                ++rit;
                break;
            case cond_assign_s:                            /* cond_assign_s */
                res   = get_locint_r();
                arg1  = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                if (*rit > 0) {
                    info.r = res;
                    info.x = arg1;
                    info.dx = 1.0;
                }
                ++rit;
                break;
            case cond_eq_assign_s:                      /* cond_eq_assign_s */
                res   = get_locint_r();
                arg1  = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                if (*rit >= 0) {
                    info.r = res;
                    info.x = arg1;
                    info.dx = 1.0;
                }
                ++rit;
                break;
            /****************************************************************/
            /*                                              REMAINING STUFF */
            /*--------------------------------------------------------------*/
            case take_stock_op:                            /* take_stock_op */
                res = get_locint_r();
                size = get_locint_r();
                get_val_v_r(size);
                break;
            case death_not:                                    /* death_not */
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                break;

            default:
                fprintf(DIAG_OUT, "Internal error in second_order_rev()"); 
                break;
        } // end switch

        // The implementation of second order reverse mode
        accumulate_derivative(info, H, adjoint, rp, rw);
      } // end if (!done)

      // get next operator
      opcode = get_op_r();
    } // end while
    myfree1(adjoint);
    free(rp);
    myfree1(rw);
    return ret_c;
}

// The public interface                   
int hessian_sparse(short tnum,  // tape id
                   int indep,   // # of indeps
                   double * basepoint,
                   int* nnz,
                   unsigned int **rind,
                   unsigned int **cind,
                   double **values)  // The dense Hessian
{
  locint* indexmap = (locint*)malloc(sizeof(locint) * indep);
  std::map<locint, locint> inv_indexmap;
  SparseHessian* H = new SparseHessian();
  int ret_c = second_order_rev(tnum, indep, basepoint, H, indexmap, inv_indexmap);
  if (ret_c < 0) {
    return ret_c;
  }
  // release any reallocated memory
  if (*rind) {free(*rind);}
  if (*cind) {free(*cind);}
  if (*values) {free(*values);}
  H->get_coo_format(indep, nnz, rind, cind, values, indexmap, inv_indexmap);
  delete H;
  free(indexmap);
  return ret_c;
}

int hessian_dense(short tnum,  // tape id
                  int indep,   // # of indeps
                  double * basepoint,
                  double** Hess)  // The dense Hessian
{

  locint* indexmap = (locint*)malloc(sizeof(locint) * indep);
  std::map<locint, locint> inv_indexmap;
  DenseHessian* H = new DenseHessian();
  int ret_c = second_order_rev(tnum, indep, basepoint, H, indexmap, inv_indexmap);
  if (ret_c < 0) {
    return ret_c;
  }
  for (int i = 0; i < indep; i++) {
    for (int j = i; j < indep; j++) {
      Hess[j][i] = H->get_val(indexmap[i], indexmap[j]);
    }
  }
  delete H;
  free(indexmap);
  return ret_c;
}

