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

#include <math.h>

static void dump_matrix(double** H, int n) {
  for (int i = 0; i < n; i++) {
    printf("H[%d, *] = ", i);
    for (int j = 0; j < n; j++) {
      printf(" %.2f ", H[i][j]);
    }
    printf("\n");
  }
}
static const locint NULL_LOC = std::numeric_limits<locint>::max();

class DerivativeInfo {
 public:
  DerivativeInfo() {
    clear();
  }

  void clear() {
    r = NULL_LOC; x = NULL_LOC; y = NULL_LOC;
    vx = 0.0; vy = 0.0;
    dx = 0.0; dy = 0.0;
    pxx = 0.0; pxy = 0.0; pyy = 0.0;
  }
  void debug() const {
    std::cout << "opcode = " << (int)opcode << " r = " << r
              << " x = " << x << " y = " << y << std::endl;
    std::cout << "dx = " << dx << " dy = " << dy 
              << " pxx = " << pxx << " pxy = " << pxy
              << " pyy = " << pyy << std::endl;
  }
  unsigned char opcode;
  locint r, x, y;
  mutable double coval; // only used by pow_d_a and pow_a_d
  double vx, vy;
  double dx, dy;
  double pxx, pxy, pyy;
};

inline static void increase(double** H, locint x, locint y, double w) {
  H[x][y] += w;
  H[y][x] += w;
}

inline static void increase_d(double** H, locint x, double w) {
  H[x][x] += w;
}

static void branch_switch_warning(const char* opname) {
  fprintf(DIAG_OUT, "ADOL-C Warning: Branch switch detected in comparison (%s).\n, Forward sweep aborted! Retaping recommended!", opname);
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
                dp_T0[res] += dp_T0[arg1]*dp_T0[arg2];
                break;
            case eq_min_d: /* Subtract a floating point from an    eq_min_d */
                /* adouble. (-=) */
                res   = get_locint_f();
                coval = get_val_f();
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
                dp_T0[res] = pow(dp_T0[arg],coval);
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
            default:
                fprintf(DIAG_OUT, "Unsupported operator (%d) in DenseHess, please email us so an update will be released.\n", opcode);
                break;
        }  // end switch
        opcode = get_op_f();
    } // end while
    end_sweep();
    myfree1(dp_T0);
    return ret_c;
}


// Evaluating Dense Hessian using Second order reverse mode
int second_order_rev(short tnum,  // tape id
                     int indep,   // # of indeps
                     double * basepoint,
                     double** Hess)  // The dense Hessian
{
    printf("Calling Second order rev, NULL_LOC = %u\n", NULL_LOC);
    
    init_rev_sweep(tnum);
    if ( (1 != ADOLC_CURRENT_TAPE_INFOS.stats[NUM_DEPENDENTS]) ||
            (indep != ADOLC_CURRENT_TAPE_INFOS.stats[NUM_INDEPENDENTS]) )
        fail(ADOLC_REVERSE_COUNTS_MISMATCH);
    int indexi = ADOLC_CURRENT_TAPE_INFOS.stats[NUM_INDEPENDENTS];
    int max_live = ADOLC_CURRENT_TAPE_INFOS.stats[NUM_MAX_LIVES];
    end_sweep();
    printf("Size of max live set = %d\n", max_live);

    std::vector<double> values;
    int ret_c = reevaluate(tnum, basepoint, max_live, values);   
    if (ret_c < 0) {
      return ret_c;
    }

    double** H = myalloc2(max_live, max_live);
    double* adjoint = myalloc1(max_live);
    double w;
    double* r = myalloc1(max_live);
    locint* indexmap = (locint*)malloc(sizeof(locint) * indexi);

    for (int i = 0; i < max_live; i++) {
        adjoint[i] = 0;
        for (int j = 0; j < max_live; j++) {
            H[i][j] = 0.0;
        }
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

    init_rev_sweep(tnum);
    opcode = get_op_r();    
    while (opcode != start_of_tape) {
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
                break;
            case assign_d:      /* assign an adouble variable a    assign_d */
                /* double value. (=) */
                res   = get_locint_r();
                coval = get_val_r();
                break;
/*
            case neg_sign_p:
            case recipr_p:
            case assign_p:
                break;
*/
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
                for (int i = indexi; i < indep; i++) {
                  Hess[i][indexi] = H[res][indexmap[i]];
                }
                // (TODO) : do something about res;
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
            //case eq_min_p: /* Subtract a floating point from an  eq_min_p */
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
            //case eq_mult_p:      /* Multiply an adouble by a    eq_mult_p */
                /* flaoting point. (*=) */
                //res   = get_locint_r();
                //arg   = get_locint_r();
                //coval = ADOLC_CURRENT_TAPE_INFOS.pTapeInfos.paramstore[arg];
                //break;
            case eq_mult_a: /* Multiply one adouble by another    eq_mult_a */
                /* (*=) */
                res = get_locint_r();
                arg = get_locint_r();
                info.r = res;
                info.x = res;
                info.y = arg;
                vy = *rit;rit++;
                vx = *rit;rit++;
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
            //case plus_a_p:     /* Add an adouble and a double    plus_a_p */
            //case min_a_p:        /* Subtract an adouble from a    min_a_p */
                break;
            case plus_d_a:       /* Add an adouble and a double    plus_d_a */
                /* (+) */
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                info.r = res;
                info.x = arg1;
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
           case min_d_a:           /* Subtract an adouble from a    min_d_a */
                /* double (-) */
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
                vy = *rit;rit++;
                vx = *rit;rit++;
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
                // (TODO)
                break;
            case eq_min_prod:   /* decrement a product of       eq_min_prod */
                /* two adoubles (*) */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                // (TODO)
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
            //case mult_a_p: /* Multiply an adouble by a double    mult_a_p */
            case div_a_a:     /* Divide an adouble by an adouble    div_a_a */
                /* (/) */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vy = *rit;rit++;
                vx = *rit;rit++;
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
                vx = *rit;rit++;
                info.dx = -coval/(vx*vx);
                info.pxx = 2.0*coval/(vx*vx*vx);
                break;
            //case div_p_a:     /* Division double - adouble (/)    div_p_a */
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
                vx = *rit;rit++;
                info.r = res;
                info.x = arg;
                info.dx = exp(vx);
                info.pxx = info.dx;
                break;
            case log_op:                                          /* log_op */
                res = get_locint_r();
                arg = get_locint_r();
                vx = *rit;rit++;
                info.r = res;
                info.x = arg;
                info.dx = 1.0/vx;
                info.pxx = -1.0/(vx*vx);
                break;
            case pow_op:                                          /* pow_op */
                res   = get_locint_r();
                arg   = get_locint_r();
                coval = get_val_r();
                vx = *rit;rit++;
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
            //case pow_op_p:                                    /* pow_op_p */ 
            case sqrt_op:                                        /* sqrt_op */
                res = get_locint_r();
                arg = get_locint_r();
                vx = *rit;rit++;
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
                vx = *rit;rit++;
                info.r = res;
                info.x = arg1;
                info.dx = cos(vx);
                info.pxx = -sin(vx);
                break;
            case cos_op:                      /* cosine operation    cos_op */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;rit++;
                info.r = res;
                info.x = arg1;
                info.dx = -sin(vx);
                info.pxx = -cos(vx);
                break;
            case atan_op:                                       /* atan_op  */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;rit++;
                info.r = res;
                info.x = arg1;
                info.dx = 1.0/(1.0+vx*vx);
                info.pxx = -(2.0*vx)/((1.0+vx*vx)*(1.0+vx*vx));
                break;
            case asin_op:                                       /* asin_op  */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;rit++;
                info.r = res;
                info.x = arg1;
                info.dx = 1.0/sqrt(1.0-vx*vx);
                info.pxx = vx/((sqrt(1.0-vx*vx))*(1.0-vx*vx));
                break;
            case acos_op:                                       /* acos_op  */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;rit++;
                info.r = res;
                info.x = arg1;
                info.dx = -1.0/sqrt(1.0-vx*vx);
                info.pxx = -vx/((sqrt(1.0-vx*vx))*(1.0-vx*vx));
                break;
            case asinh_op:                                      /* asinh_op */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;rit++;
                info.r = res;
                info.x = arg1;
                info.dx = 1.0/sqrt(1.0+vx*vx);
                info.pxx = -vx*info.dx/(1.0+vx*vx);
                break;
            case acosh_op:                                      /* acosh_op */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;rit++;
                info.r = res;
                info.x = arg1;
                info.dx = 1.0/sqrt(vx*vx-1.0);
                info.pxx = -vx*info.dx/(vx*vx-1.0);
                break;
            case atanh_op:                                      /* atanh_op */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;rit++;
                info.r = res;
                info.x = arg1;
                info.dx = 1/(1-vx*vx);
                info.pxx = 2.0*vx*info.dx*info.dx;
                break;
            case erf_op:                                        /* erf_op   */
                res  = get_locint_r();
                arg2 = get_locint_r();
                arg1 = get_locint_r();
                vx = *rit;rit++;
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
                rit++;
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
                rit++;
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
                rit++;
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
                rit++;
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
                rit++;
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
                rit++;
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
        if (info.r != NULL_LOC) {
            // Step 0: pseudo binary function
            if (info.x != NULL_LOC && info.x == info.y) {
              info.dx += info.dy; info.dy = 0;
              info.pxx += info.pyy + 2.0 * info.pxy;
              info.pyy = info.pxy = 0;
              info.y = NULL_LOC;
            }
            // Step 1: retrieve w and r
            w = adjoint[info.r]; adjoint[info.r] = 0.0;
            for (int i = 0; i < max_live; i++) {
                r[i] = H[info.r][i];
                H[info.r][i] = 0; H[i][info.r] = 0;
            }
            // Step 2: accumulate adjoints
            if (info.x != NULL_LOC) {
                adjoint[info.x] += info.dx * w;
            }
            if (info.y != NULL_LOC) {
                adjoint[info.y] += info.dy * w;
            }
            // Step 3: accumulate Hessian
            double pw = 0.0;
            for (locint p = 0; p < max_live; p++) {
               if ((pw = r[p]) != 0) {
                   if (info.y != NULL_LOC) {
                       if (info.r != p) {
                           if (info.x == p) {
                               increase_d(H, p, 2*info.dx*pw);
                           } else {
                               increase(H, info.x, p, info.dx*pw);
                           }
                           if (info.y == p) {
                               increase_d(H, p, 2*info.dy*pw);
                           } else {
                               increase(H, info.y, p, info.dy*pw);
                           }
                       } else { // info.r == p, self edge
                           increase_d(H, info.x, info.dx*info.dx*pw);
                           increase_d(H, info.y, info.dy*info.dy*pw);
                           increase(H, info.x, info.y, info.dx*info.dy*pw);
                       }
                   } else if (info.x != NULL_LOC) {
                       if (info.r != p) {
                           if (info.x == p) {
                               increase_d(H, p, 2*info.dx*pw);
                           } else {
                               increase(H, info.x, p, info.dx*pw);
                           }
                       } else {
                           increase_d(H, info.x, info.dx*info.dx*pw);
                       }
                   }
               } // end pw != 0.0
            } // end for
            if (w != 0) {
                if (info.pxx != 0.0) {
                    increase_d(H, info.x, info.pxx * w);
                }
                if (info.pyy != 0.0) {
                    increase_d(H, info.y, info.pyy * w);
                }
                if (info.pxy != 0.0) {
                    increase(H, info.x, info.y, info.pxy * w);
                }
            }
        } // end info.r != NULL_LOC
        opcode = get_op_r();
        info.clear();
    } // end while
    myfree2(H);
    myfree1(adjoint);
    myfree1(r);
    free(indexmap);
    return ret_c;
}
