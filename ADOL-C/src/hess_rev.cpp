#include <adolc/interfaces.h>
#include <adolc/adalloc.h>
#include "oplate.h"
#include "taping_p.h"
#include <adolc/convolut.h>
#include "dvlparms.h"

#include <math.h>

// A forward mode reevaluation for the intermediate values
void reevaluate(short tnum,
                const double * const basepoint,
                int max_live,
                std::vector<double>& values) {
    double* dp_T0 = myalloc1(max_live);
    init_for_sweep(tnum);
    unsigned char opcode;
    locint res  = 0;
    locint arg  = 0;
    locint arg1 = 0;
    locint arg2 = 0;
    double coval;    
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
            case neq_zero :                                     /* neq_zero */
            case le_zero  :                                      /* le_zero */
            case gt_zero  :                                      /* gt_zero */
            case ge_zero  :                                      /* ge_zero */
            case lt_zero  :                                      /* lt_zero */
                arg  = get_locint_f();
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
                dp_T0[res]=dp_T0[arg1]/dp_T0[arg2];
                break;
            case div_d_a:       /* Division double - adouble (/)    div_d_a */
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
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
                dp_T0[res]= exp(dp_T0[arg]);
                break;
            case log_op:                                         /* log_op */
                arg  = get_locint_f();
                res  = get_locint_f();
                dp_T0[res]= log(dp_T0[arg]);
                break;
            case pow_op:                                         /* pow_op */
                arg  = get_locint_f();
                res  = get_locint_f();
                coval   = get_val_f();
                dp_T0[res] = pow(dp_T0[arg],coval);
                break;
            case sqrt_op:                                       /* sqrt_op */
                arg  = get_locint_f();
                res  = get_locint_f();
                dp_T0[res]= sqrt(dp_T0[arg]);
                break;
            case sin_op:                       /* sine operation    sin_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                dp_T0[arg2]= cos(dp_T0[arg1]);
                dp_T0[res] = sin(dp_T0[arg1]);
                break;
            case cos_op:                     /* cosine operation    cos_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                dp_T0[arg2]= sin(dp_T0[arg1]);
                dp_T0[res] = cos(dp_T0[arg1]);
                break;
            case atan_op:                                       /* atan_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                dp_T0[res] = atan(dp_T0[arg1]);
                break;
            case asin_op:                                       /* asin_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                dp_T0[res] = asin(dp_T0[arg1]);
                break;
            case acos_op:                                       /* acos_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                dp_T0[res] = acos(dp_T0[arg1]);
                break;

#ifdef ATRIG_ERF
            case asinh_op:                                     /* asinh_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                dp_T0[res] = asinh(dp_T0[arg1]);
                break;
            case acosh_op:                                     /* acosh_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                dp_T0[res] = acosh(dp_T0[arg1]);
                break;
            case atanh_op:                                     /* atanh_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                dp_T0[res] = atanh(dp_T0[arg1]);
                break;
            case erf_op:                                         /* erf_op */
                arg1 = get_locint_f();
                arg2 = get_locint_f();
                res  = get_locint_f();
                dp_T0[res] = erf(dp_T0[arg1]);
                break;
#endif

            case min_op:                                         /* min_op */
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                if (dp_T0[arg1] > dp_T0[arg2])
                    dp_T0[res] = dp_T0[arg2];
                else
                    dp_T0[res] = dp_T0[arg1];
                break;
            case abs_val:                                       /* abs_val */
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                dp_T0[res]  = fabs(dp_T0[arg]);
                break;
            case ceil_op:          /* Compute ceil of adouble      ceil_op */
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                dp_T0[res]  = ceil(dp_T0[arg]);
                break;
            case floor_op:         /* Compute floor of adouble    floor_op */
                arg   = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                dp_T0[res]  = floor(dp_T0[arg]);
                break;

            case cond_assign:                               /* cond_assign */
                arg   = get_locint_f();
                arg1  = get_locint_f();
                arg2  = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                if (dp_T0[arg]>0){
                    if (coval<=0){
                        fprintf(DIAG_OUT,"Inconsistency in cond_assign. Retape?\n");
                    }
                    dp_T0[res]=dp_T0[arg1];
                }
                else{
                    if (coval>0){
                        fprintf(DIAG_OUT,"Inconsistency in cond_assign. Retape?\n");
                    }
                    dp_T0[res]=dp_T0[arg2];
                }
                break;
            case cond_assign_s:                           /* cond_assign_s */
                arg   = get_locint_f();
                arg1  = get_locint_f();
                res   = get_locint_f();
                coval = get_val_f();
                if (dp_T0[arg]>0) {
                    if (coval<=0){
                        fprintf(DIAG_OUT,"Inconsistency in cond_assign_s. Retape?\n");
                    }
                    dp_T0[res]=dp_T0[arg1];
                }
                break;
            default:
                fprintf(DIAG_OUT, "Unsupported operator in DenseHess, please email us so an update will be released.\n", opcode);
                break;
        }  // end switch
        opcode = get_op_f();
    } // end while
    end_sweep();
    myfree1(dp_T0);
}


// Evaluating Dense Hessian using Second order reverse mode
int second_order_rev(short tnum,  // tape id
                     int indep,   // # of indeps
                     double * basepoint,
                     double** Hess)  // The dense Hessian
{
    printf("Calling DenseHess\n");
    exit(-1);
    
    init_rev_sweep(tnum);
    if ( (1 != ADOLC_CURRENT_TAPE_INFOS.stats[NUM_DEPENDENTS]) ||
            (indep != ADOLC_CURRENT_TAPE_INFOS.stats[NUM_INDEPENDENTS]) )
        fail(ADOLC_REVERSE_COUNTS_MISMATCH);
    int indexi = ADOLC_CURRENT_TAPE_INFOS.stats[NUM_INDEPENDENTS] - 1;
    int indexd = ADOLC_CURRENT_TAPE_INFOS.stats[NUM_DEPENDENTS] - 1;
    int max_live = ADOLC_CURRENT_TAPE_INFOS.stats[NUM_MAX_LIVES];
    end_sweep();
    double** H = myalloc2(max_live, max_live);
    double* adjoint = myalloc1(max_live);
    std::vector<double> intermediate_values;
    reevaluate(tnum, basepoint, max_live, intermediate_values);   

    for (int i = 0; i < max_live; i++) {
        adjoint[i] = 0;
        for (int j = 0; j < max_live; j++) {
            H[i][j] = 0.0;
        }
    }

    int ret_c = 3;
    unsigned char opcode;
    locint size = 0;
    locint res  = 0;
    locint arg  = 0;
    locint arg1 = 0;
    locint arg2 = 0;
    double coval = 0;

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
                arg   = get_locint_r();
                ret_c = 0;
                break;
            case neq_zero :                                     /* neq_zero */
            case gt_zero  :                                      /* gt_zero */
            case lt_zero :                                       /* lt_zero */
                arg   = get_locint_r();
                break;
            case ge_zero :                                       /* ge_zero */
            case le_zero :                                       /* le_zero */
                arg   = get_locint_r();
                ret_c = 0;
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
                break;
            case assign_ind: /* assign an adouble variable an    assign_ind */
                /* independent double value (<<=) */
                res = get_locint_r();
                break;
            case assign_dep:     /* assign a float variable a    assign_dep */
                /* dependent adouble value. (>>=) */
                res = get_locint_r();
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
                break;

            case eq_mult_d:        /* Multiply an adouble by a    eq_mult_d */
                /* flaoting point. (*=) */
                res   = get_locint_r();
                coval = get_val_r();
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
                break;
        
            case incr_a:                  /* Increment an adouble    incr_a */
            case decr_a:                 /* Increment an adouble    decr_a */
                res   = get_locint_r();
                break;
            default:
                fprintf(DIAG_OUT, "An internal error in densehess().\n");
        } // end switch
        opcode = get_op_r();
    } // end while
    end_sweep();

    myfree2(H);
    myfree1(adjoint);
    return 0;
}
