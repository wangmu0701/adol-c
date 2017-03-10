#ifndef ADOLC_HESS_REV_H_
#define ADOLC_HESS_REV_H_

#include <adolc/internal/common.h>

ADOLC_DLL_EXPORT int hessian_dense(short, int, double*, double**);

ADOLC_DLL_EXPORT int hessian_sparse(short, int, double*, int*,
                                    unsigned int**, unsigned int**, double**);

#endif // ADOLC_HESS_REV_H_
