/*
 * omrjit.h
 *
 *  Created on: Sep. 22, 2020
 *      Author: debajyoti
 */

#ifndef SRC_INCLUDE_JIT_OMRJIT_H_
#define SRC_INCLUDE_JIT_OMRJIT_H_

bool omr_provider_successfully_loaded;
bool provider_init(void);

typedef int32_t (*omr_eval_compile)();
omr_eval_compile omreval_compile;

/*typedef int32_t (*omr_eval_exec)(int32_t a, int32_t b);
omr_eval_exec omreval_exec;*/

typedef bool (*omr_eval_initialize)();
omr_eval_initialize omreval_init;

typedef void (*omr_eval_shutdown)();
omr_eval_shutdown omreval_shut;

char	omrjit_path[MAXPGPATH];

typedef void (OMRJIT_slot_deformFunctionType)(int32_t, TupleTableSlot *, HeapTuple , uint32 *);
OMRJIT_slot_deformFunctionType *slot_deform;


#endif /* SRC_INCLUDE_JIT_OMRJIT_H_ */
