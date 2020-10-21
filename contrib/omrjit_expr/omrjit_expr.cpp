/*
 * omrjit_expr.cpp
 *
 *  Created on: Aug. 8, 2020
 *      Author: debajyoti
 */

/*
 * JIT compile expression.
 */

extern "C" {

#include "postgres.h"

#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "parser/parse_coerce.h"
#include "parser/parsetree.h"
#include "pgstat.h"
#include "utils/acl.h"
#include "utils/builtins.h"
#include "utils/date.h"
#include "utils/fmgrtab.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/timestamp.h"
#include "utils/typcache.h"
#include "utils/xml.h"

#include "access/htup_details.h"
#include "access/nbtree.h"
#include "access/tupconvert.h"
#include "catalog/objectaccess.h"
#include "catalog/pg_type.h"
#include "executor/execdebug.h"
#include "executor/nodeAgg.h"
#include "executor/nodeSubplan.h"
#include "executor/execExpr.h"
#include "funcapi.h"

#include "executor/tuptable.h"
#include "nodes/nodes.h"
#include "access/attnum.h"
#include "c.h"
#include "access/tupmacs.h"

#include "postgres.h"
#include "executor/execExpr.h"
#include "jit/jit.h"
#include "executor/tuptable.h"
#include "nodes/nodes.h"
#include "jit/omrjit.h"

}//extern block ended

#include "/home/debajyoti/vm-project/src/lib/omr/jitbuilder/release/cpp/include/JitBuilder.hpp"
#include <iostream>
using std::cout;
using std::cerr;


extern "C" {


/*Initialize omr*/
bool omr_init(){
    bool initialized = initializeJit();
    return initialized;
}

/*Shutdown omr*/
void omr_shut(){
    shutdownJit();
}

//VARSIZE_ANY_func
static int32_t VARSIZE_ANY_func(char* attptr) {
    #define VARSIZE_ANY_func_LINE LINETOSTR(__LINE__)

	return (VARSIZE_ANY(attptr));
}

//t_uint32_func
static int32_t t_uint32_func(char *T) {
    #define t_uint32_func_LINE LINETOSTR(__LINE__)

	return *((uint8 *) (T));
}

//t_datum_func
static Datum t_datum_func(char *T) {
    #define t_datum_func_LINE LINETOSTR(__LINE__)

	return *((Datum *)(T));
}

//t_int32_func
static Datum t_int32_func(char *T) {
    #define t_int32_func_LINE LINETOSTR(__LINE__)

	return Int32GetDatum(*((int32 *)(T)));
}

//t_int16_func
static Datum t_int16_func(char *T) {
    #define t_int16_func_LINE LINETOSTR(__LINE__)

	return Int16GetDatum(*((int16 *)(T)));
}

//t_str_func
static Datum t_str_func(char *T) {
    #define t_str_func_LINE LINETOSTR(__LINE__)

	return CharGetDatum(*((char *)(T)));
}


//strlen_func
static int32_t strlen_func(char* attptr) {
    #define strlen_func_LINE LINETOSTR(__LINE__)

	return (strlen((char *) (attptr)));
}

static void store_isnull(TupleTableSlot *slot, int16_t index) {
    #define ISNULL_LINE LINETOSTR(__LINE__)
	bool	   *isnull = slot->tts_isnull;
	isnull[index] = true;
}
static void print_func(int32_t m, int32_t n) {
    #define PRINTFUNC_LINE LINETOSTR(__LINE__)

	elog(INFO, "natts in print: %d\n", m);
	elog(INFO, "natts in print: %d\n", n);

}


static char* tp_func(HeapTupleHeader tup) {
    #define TPFUNC_LINE LINETOSTR(__LINE__)

	return ((char *) tup + tup->t_hoff);

}

/* return att_align_nominal */
static int32_t att_addlength_pointer_func(int32_t off, int16_t attlen, char * attptr/*HeapTupleHeader tup*/) {
    #define ATTADDLENFUNC_LINE LINETOSTR(__LINE__)
	//elog(INFO, "tp1: %d\n", (Datum*)attptr);
	//elog(INFO, "attlen: %d\n", attlen);
	//elog(INFO, "attptr: %s\n", attptr);
	return att_addlength_pointer(off, attlen, attptr/*+off*//*(char *) tup + tup->t_hoff + off*/);

}

/* return fetchatt */
static Datum fetchatt_func(Form_pg_attribute A, char * T/*HeapTupleHeader tup*/, int32_t off) {
    #define FETCHATTFUNC_LINE LINETOSTR(__LINE__)

	return fetchatt(A, /*(char *) tup + tup->t_hoff + off*/T);

}

/* return att_align_nominal */
static int32_t att_align_nominal_func(int32_t cur_offset, char attalign) {
    #define ATTALIGNNOMINALFUNC_LINE LINETOSTR(__LINE__)
	//elog(INFO, "attlen: %d\n", cur_offset);
	//elog(INFO, "attlen: %d\n", att_align_nominal(cur_offset, attalign));
	return att_align_nominal(cur_offset, attalign);

}


/* return att_align_pointer */
static int32_t att_align_pointer_func(int32_t cur_offset, char attalign, int32_t attlen, char * attptr/*HeapTupleHeader tup*/) {
    #define ATTALIGNPTRFUNC_LINE LINETOSTR(__LINE__)

	return att_align_pointer(cur_offset, attalign, attlen, /*(char *) tup + tup->t_hoff*/attptr + cur_offset);

}


static uint32 slot_test(TupleTableSlot *slot, HeapTuple tuple, /*uint32*/bool /**offp*/ *slow_test, int16_t natts, HeapTupleHeader tup, bool hasnulls
		,Datum *values, bool *isnull, bits8 *bp, TupleDesc tupleDesc, int attnum, uint32 off, bool slow, FormData_pg_attribute *thisatt/*, char *tp*/)
{

#define SLOTTEST_LINE LINETOSTR(__LINE__)

	//elog(INFO, "natts: %d\n", natts);
	//elog(INFO, "thisatt1->attcacheoff: %d\n", thisatt1->attcacheoff);
	//TupleDesc	tupleDesc = slot->tts_tupleDescriptor;

	//values = slot->tts_values;

	//bool	   *isnull = slot->tts_isnull;
	//HeapTupleHeader tup = tuple->t_data;

	//elog(INFO, "hasnulls1: %d\n", hasnulls);
	//bool hasnulls = HeapTupleHasNulls(tuple);
	//elog(INFO, "hasnulls2: %d\n", hasnulls);

	//int			attnum;
	char	   *tp;				/* ptr to tuple data */
	//uint32		off;			/* offset in tuple data */
	//bits8	   *bp = tup->t_bits;	/* ptr to null bitmap in tuple */
	//bool		slow;			/* can we use/set attcacheoff? */

	/* We can only fetch as many attributes as the tuple has. */
	//natts = Min(HeapTupleHeaderGetNatts(tuple->t_data), natts);


	/*
	 * Check whether the first call for this tuple, and initialize or restore
	 * loop state.
	 */
	//attnum = slot->tts_nvalid;
	/*if (attnum == 0)
	{
		 Start from the first attribute
		off = 0;
		slow = false;
	}
	else
	{
		 Restore state from previous execution
		off = *offp;
		slow = TTS_SLOW(slot);
	}*/

	tp = (char *) tup + tup->t_hoff;
	//elog(INFO, "tp: %d\n", (Datum*)tp);
	//for (; attnum < natts; attnum++)
	//{
		//Form_pg_attribute thisatt = TupleDescAttr(tupleDesc, attnum);
		//elog(INFO, "thisatt->attcacheoff: %d\n", thisatt->attcacheoff);
		//Form_pg_attribute thisatt = attrs[attnum];
		//elog(INFO, "thisatt->attlen: %d\n", thisatt->attlen);

		/*if (hasnulls && att_isnull(attnum, bp))
		{
			values[attnum] = (Datum) 0;
			isnull[attnum] = true;
			*slow_test = true;		 //can't use attcacheoff anymore
			//continue;
			return off;
		}*/

		//isnull[attnum] = false;

		if (!(*slow_test) && thisatt->attcacheoff >= 0)
			off = thisatt->attcacheoff;
		else if (thisatt->attlen == -1)
		{
			////*
			 ///* We can only cache the offset for a varlena attribute if the
			 ///* offset is already suitably aligned, so that there would be no
			 ////* pad bytes in any case: then the offset will be valid for either
			 ////* an aligned or unaligned value.
			 ///
			if (!(*slow_test) &&
				off == att_align_nominal(off, thisatt->attalign))
				thisatt->attcacheoff = off;
			else
			{
				off = att_align_pointer(off, thisatt->attalign, -1,
										tp + off);
				*slow_test = true;
			}
		}
		else
		{
			///* not varlena, so safe to use att_align_nominal
			off = att_align_nominal(off, thisatt->attalign);

			if (!(*slow_test))
				thisatt->attcacheoff = off;
		}

		values[attnum] = fetchatt(thisatt, tp + off);
		off = att_addlength_pointer(off, thisatt->attlen, tp + off);

		/*if (thisatt->attlen <= 0)
			*slow_test = true;*/		/* can't use attcacheoff anymore */
	//}

	/*
	 * Save state for next execution
	 */
	//slot->tts_nvalid = attnum;
	//*offp = off;
	/*if (slow)
		slot->tts_flags |= TTS_FLAG_SLOW;
	else
		slot->tts_flags &= ~TTS_FLAG_SLOW;*/

	return off;

}



static void slot_deform_heap_tuple(TupleTableSlot *slot, HeapTuple tuple, uint32 *offp, int natts){

    #define DEFORM_LINE LINETOSTR(__LINE__)

	TupleDesc	tupleDesc = slot->tts_tupleDescriptor;
	Datum	   *values = slot->tts_values;
	bool	   *isnull = slot->tts_isnull;
	HeapTupleHeader tup = tuple->t_data;
	bool		hasnulls = HeapTupleHasNulls(tuple);
	int			attnum;
	char	   *tp;				/* ptr to tuple data */
	uint32		off;			/* offset in tuple data */
	bits8	   *bp = tup->t_bits;	/* ptr to null bitmap in tuple */
	bool		slow;			/* can we use/set attcacheoff? */

	/* We can only fetch as many attributes as the tuple has. */
	natts = Min(HeapTupleHeaderGetNatts(tuple->t_data), natts);

	/*
	 * Check whether the first call for this tuple, and initialize or restore
	 * loop state.
	 */
	attnum = slot->tts_nvalid;
	if (attnum == 0)
	{
		/* Start from the first attribute */
		off = 0;
		slow = false;
	}
	else
	{
		/* Restore state from previous execution */
		off = *offp;
		slow = TTS_SLOW(slot);
	}

	tp = (char *) tup + tup->t_hoff;

	for (; attnum < natts; attnum++)
	{
		elog(INFO, "natts: %d\n", natts);
		Form_pg_attribute thisatt = TupleDescAttr(tupleDesc, attnum);

		if (hasnulls && att_isnull(attnum, bp))
		{
			values[attnum] = (Datum) 0;
			isnull[attnum] = true;
			slow = true;		/* can't use attcacheoff anymore */
			continue;
		}

		isnull[attnum] = false;

		if (!slow && thisatt->attcacheoff >= 0)
			off = thisatt->attcacheoff;
		else if (thisatt->attlen == -1)
		{
			/*
			 * We can only cache the offset for a varlena attribute if the
			 * offset is already suitably aligned, so that there would be no
			 * pad bytes in any case: then the offset will be valid for either
			 * an aligned or unaligned value.
			 */
			if (!slow &&
				off == att_align_nominal(off, thisatt->attalign))
				thisatt->attcacheoff = off;
			else
			{
				off = att_align_pointer(off, thisatt->attalign, -1,
										tp + off);
				slow = true;
			}
		}
		else
		{
			/* not varlena, so safe to use att_align_nominal */
			off = att_align_nominal(off, thisatt->attalign);

			if (!slow)
				thisatt->attcacheoff = off;
		}

		values[attnum] = fetchatt(thisatt, tp + off);

		off = att_addlength_pointer(off, thisatt->attlen, tp + off);

		if (thisatt->attlen <= 0)
			slow = true;		/* can't use attcacheoff anymore */
	}

	/*
	 * Save state for next execution
	 */
	slot->tts_nvalid = attnum;
	*offp = off;
	if (slow)
		slot->tts_flags |= TTS_FLAG_SLOW;
	else
		slot->tts_flags &= ~TTS_FLAG_SLOW;

}

}//extern C block ended



/****************Define class******************/

/*typedef void (OMRJIT_slot_deformFunctionType)(int32_t, TupleTableSlot *, HeapTuple , uint32 *);
OMRJIT_slot_deformFunctionType *slot_deform;*/
class slot_compile_deform : public OMR::JitBuilder::MethodBuilder
   {
   private:

   OMR::JitBuilder::IlType *pStr;
   OMR::JitBuilder::IlType *pChar;
   OMR::JitBuilder::IlType *pDatum;
   OMR::JitBuilder::IlType *pDat;
   OMR::JitBuilder::IlType *pBits;
   OMR::JitBuilder::IlType *pInt32;
   OMR::JitBuilder::IlType *pInt16;
   OMR::JitBuilder::IlType *pBits8;
   OMR::JitBuilder::IlType *bool_type;
   OMR::JitBuilder::IlType *pbool;
   OMR::JitBuilder::IlType *size_t_type;
   OMR::JitBuilder::IlType *puint32;
   OMR::JitBuilder::IlType *datum_rep;
   OMR::JitBuilder::IlType *int32_rep;
   OMR::JitBuilder::IlType *int16_rep;
   OMR::JitBuilder::IlType *str_rep;

   OMR::JitBuilder::IlType *StructTypeContext;
   OMR::JitBuilder::IlType *pStructTypeContext;

   OMR::JitBuilder::IlType *StructTypeTupleDesc;
   OMR::JitBuilder::IlType *pStructTypeTupleDesc;

   OMR::JitBuilder::IlType *StructTypeSlotOps;
   OMR::JitBuilder::IlType *pStructTypeSlotOps;

   OMR::JitBuilder::IlType *FormData_pg_attribute;
   OMR::JitBuilder::IlType *pFormData_pg_attribute;

   //OMR::JitBuilder::IlType *TupleTableSlot;
   //OMR::JitBuilder::IlType *pTupleTableSlot;

   OMR::JitBuilder::IlType *HeapTupleHeaderData;
   OMR::JitBuilder::IlType *pHeapTupleHeaderData;

   OMR::JitBuilder::IlType *HeapTuple;
   OMR::JitBuilder::IlType *pHeapTuple;

   OMR::JitBuilder::IlType *HeapTupleData;
   OMR::JitBuilder::IlType *pHeapTupleData;

   OMR::JitBuilder::IlType *TupleTableSlotType;
   OMR::JitBuilder::IlType *pTupleTableSlot;



   public:

      slot_compile_deform(OMR::JitBuilder::TypeDictionary *);

      OMR::JitBuilder::IlValue* fetch_attributes(IlBuilder *, OMR::JitBuilder::IlValue *, OMR::JitBuilder::IlValue *, OMR::JitBuilder::IlValue *);
      OMR::JitBuilder::IlValue* att_align_nominal_cal(IlBuilder *, OMR::JitBuilder::IlValue *, OMR::JitBuilder::IlValue *);
      OMR::JitBuilder::IlValue* att_addlength_pointer_cal(IlBuilder *b, OMR::JitBuilder::IlValue *, OMR::JitBuilder::IlValue *, OMR::JitBuilder::IlValue *);
      OMR::JitBuilder::IlValue* att_align_pointer_cal(IlBuilder *, OMR::JitBuilder::IlValue *, OMR::JitBuilder::IlValue *,
      		OMR::JitBuilder::IlValue *, OMR::JitBuilder::IlValue *);

      virtual bool buildIL();

   };

/****************************************Define the method builder object********************************************************/

slot_compile_deform::slot_compile_deform(OMR::JitBuilder::TypeDictionary *types)
   : OMR::JitBuilder::MethodBuilder(types)
   {
   DefineLine(LINETOSTR(__LINE__));
   DefineFile(__FILE__);

   DefineName("slot_compile_deform");

   pStr = types->toIlType<char *>();
   pChar = types->toIlType<char>();
   pDatum = types->toIlType<Datum *>();
   pDat = types->toIlType<Datum>();
   pBits = types->toIlType<char>();
   pInt32 = types->PointerTo(Int32);
   pInt16 = types->PointerTo(Int16);

   pBits8 = types->toIlType<bits8 *>();

   bool_type = types->toIlType<bool>();
   pbool = types->toIlType<bool*>();

   size_t_type = types->toIlType<size_t>();

   puint32 = types->toIlType<uint32>();

   datum_rep = types->PointerTo(pDatum);
   int32_rep = types->PointerTo(pInt32);
   int16_rep = types->PointerTo(pInt16);
   str_rep   = types->PointerTo(pStr);


   //StructTypeContext      = types->LookupStruct("OMRJitContext");
   //pStructTypeContext     = types->PointerTo(StructTypeContext);

   //StructTypeTupleDesc      = types->LookupStruct("TupleDesc");
   //pStructTypeTupleDesc     = types->PointerTo(StructTypeTupleDesc);

   //StructTypeSlotOps      = types->LookupStruct("TupleTableSlotOps");
   //pStructTypeSlotOps     = types->PointerTo(StructTypeSlotOps);

   FormData_pg_attribute      = types->LookupStruct("FormData_pg_attribute");
   pFormData_pg_attribute     = types->PointerTo((char *)"FormData_pg_attribute");

   //TupleTableSlotType      = types->LookupStruct("TupleTableSlot");
   //pTupleTableSlot     = types->PointerTo(TupleTableSlot);

   StructTypeTupleDesc = types->LookupStruct("TupleDescData");
   pStructTypeTupleDesc = types->PointerTo((char *)"TupleDescData");

   pTupleTableSlot = types->PointerTo((char *)"TupleTableSlot");

   HeapTuple      = types->LookupStruct("HeapTupleData");
   pHeapTuple     = types->PointerTo(HeapTuple);

   HeapTupleHeaderData      = types->LookupStruct("HeapTupleHeaderData");
   pHeapTupleHeaderData     = types->PointerTo((char *)"HeapTupleHeaderData");

   /* define Parameters */
   //DefineParameter("context",  pStructTypeContext);
   //DefineParameter("desc",     pStructTypeTupleDesc);

   DefineParameter("natts",    Int32);

   DefineParameter("slot",     pTupleTableSlot);
   DefineParameter("tuple",    HeapTuple);

   DefineParameter("offp",     pInt32);

   DefineFunction((char *)"t_uint32_func",
                  (char *)__FILE__,
                  (char *)t_uint32_func_LINE,
                  (void *)&t_uint32_func,
                  Int32,
                  1,
				  pStr);

   DefineFunction((char *)"t_datum_func",
                  (char *)__FILE__,
                  (char *)t_datum_func_LINE,
                  (void *)&t_datum_func,
                  Address,
                  1,
				  pStr);

   DefineFunction((char *)"t_int32_func",
                  (char *)__FILE__,
                  (char *)t_int32_func_LINE,
                  (void *)&t_int32_func,
                  Address,
                  1,
				  pStr);

   DefineFunction((char *)"t_int16_func",
                  (char *)__FILE__,
                  (char *)t_int16_func_LINE,
                  (void *)&t_int16_func,
                  Address,
                  1,
				  pStr);

   DefineFunction((char *)"t_str_func",
                  (char *)__FILE__,
                  (char *)t_str_func_LINE,
                  (void *)&t_str_func,
                  Address,
                  1,
				  pStr);

   //att_align_pointer_func
   DefineFunction((char *)"att_align_pointer_func",
                  (char *)__FILE__,
                  (char *)ATTALIGNPTRFUNC_LINE,
                  (void *)&att_align_pointer_func,
                  Int32,
                  4,
                  Int32, pChar, Int32, pStr/*HeapTupleHeaderData*/);

   //fetchatt_func
   DefineFunction((char *)"fetchatt_func",
                  (char *)__FILE__,
                  (char *)FETCHATTFUNC_LINE,
                  (void *)&fetchatt_func,
                  pDat,
                  3,
				  Address, pStr/*HeapTupleHeaderData*/, Int32);

   //att_align_nominal_func
   DefineFunction((char *)"att_align_nominal_func",
                  (char *)__FILE__,
                  (char *)ATTALIGNNOMINALFUNC_LINE,
                  (void *)&att_align_nominal_func,
                  Int32,
                  2,
				  Int32, pChar);

   DefineFunction((char *)"tp_func",
                  (char *)__FILE__,
                  (char *)TPFUNC_LINE,
                  (void *)&tp_func,
                  pStr,
                  1,
				  HeapTupleHeaderData);

   //VARSIZE_ANY_func
   DefineFunction((char *)"VARSIZE_ANY_func",
                  (char *)__FILE__,
                  (char *)VARSIZE_ANY_func_LINE,
                  (void *)&VARSIZE_ANY_func,
                  Int32,
                  1,
				  pStr);

   //strlen_func
   DefineFunction((char *)"strlen_func",
                  (char *)__FILE__,
                  (char *)strlen_func_LINE,
                  (void *)&strlen_func,
                  Int32,
                  1,
				  pStr);

   /* Define Return type */
   DefineReturnType(NoType);

   //att_align_nominal_func
   DefineFunction((char *)"att_addlength_pointer_func",
                  (char *)__FILE__,
                  (char *)ATTADDLENFUNC_LINE,
                  (void *)&att_addlength_pointer_func,
                  Int32,
                  3,
				  Int32, Int16, pStr/*HeapTupleHeaderData*/);

   DefineFunction((char *)"print_func",
                  (char *)__FILE__,
                  (char *)PRINTFUNC_LINE,
                  (void *)&print_func,
				  NoType,
                  2,
				  Int32,
				  Int32);

   DefineFunction((char *)"slot_deform_heap_tuple",
                  (char *)__FILE__,
                  (char *)DEFORM_LINE,
                  (void *)&slot_deform_heap_tuple,
				  NoType,
                  4,
				  Int32, pChar, pInt32, Int16);

   DefineFunction((char *)"store_isnull",
                  (char *)__FILE__,
                  (char *)ISNULL_LINE,
                  (void *)&store_isnull,
				  NoType,
                  2,
				  Int32, Int16);

   DefineFunction((char *)"slot_test",
                  (char *)__FILE__,
                  (char *)SLOTTEST_LINE,
                  (void *)&slot_test,
				  Int32,
                  14,
				  Int32, pChar, pInt32, pStr, HeapTupleHeaderData, bool_type, pDatum, pbool, pBits8, pChar, Int16, Int32, bool_type, Address);

   /* Define Return type */
   DefineReturnType(NoType);

   }

class StructTypeDictionary : public OMR::JitBuilder::TypeDictionary
   {
   public:
	  //OMR::JitBuilder::IlType *HeapTupleDataType;
	  //OMR::JitBuilder::IlType *pHeapTupleData;
   StructTypeDictionary() :
      OMR::JitBuilder::TypeDictionary()
      {




           auto d = TypeDictionary{};

           OMR::JitBuilder::IlType *t_field3Type = DefineUnion("t_field3");
      	   UnionField("t_field3", "t_cid", Int32);
     	   UnionField("t_field3", "t_xvac", Int32);
      	   CloseUnion("t_field3");

           OMR::JitBuilder::IlType *HeapTupleFieldsType = DefineStruct("HeapTupleFields");
           DefineField("HeapTupleFields", "t_xmin", Int32);
           DefineField("HeapTupleFields", "t_xmax", Int32);
           DefineField("HeapTupleFields", "t_field3", t_field3Type);

           CloseStruct("HeapTupleFields");

      	   OMR::JitBuilder::IlType *DatumTupleFieldsType = DefineStruct("DatumTupleFields");
      	   DefineField("DatumTupleFields", "datum_len_", Int32);
      	   DefineField("DatumTupleFields", "datum_typmod", Int32);
      	   DefineField("DatumTupleFields", "datum_typeid", Int32);//Oid datum_typeid;

      	   CloseStruct("DatumTupleFields");

           OMR::JitBuilder::IlType *t_choiceType = DefineUnion("t_choice");
      	   UnionField("t_choice", "t_heap", HeapTupleFieldsType);
     	   UnionField("t_choice", "t_datum", DatumTupleFieldsType);
      	   CloseUnion("t_choice");

      	   ///////////BlockIdData and ItemPointerData
      	   OMR::JitBuilder::IlType *BlockIdDataType = DefineStruct("BlockIdData");
      	   DefineField("BlockIdData", "bi_hi", Int16);
      	   DefineField("BlockIdData", "bi_lo", Int16);

      	   CloseStruct("BlockIdData");

      	   OMR::JitBuilder::IlType *ItemPointerDataType = DefineStruct("ItemPointerData");
      	   DefineField("ItemPointerData", "ip_blkid", BlockIdDataType);
      	   DefineField("ItemPointerData", "ip_posid", Int16);

      	   CloseStruct("ItemPointerData");

	   	   /****Declare HeapTupleHeaderData*********/
	   	   OMR::JitBuilder::IlType *HeapTupleHeaderDataType = DefineStruct("HeapTupleHeaderData");

	   	   DefineField("HeapTupleHeaderData", "t_choice", t_choiceType);
	   	   DefineField("HeapTupleHeaderData", "t_ctid", ItemPointerDataType);
	   	   DefineField("HeapTupleHeaderData", "t_infomask2", Int16);
	   	   DefineField("HeapTupleHeaderData", "t_infomask", Int16);
	   	   DefineField("HeapTupleHeaderData", "t_hoff", d.toIlType<uint8>());
	   	   DefineField("HeapTupleHeaderData", "t_bits", d.toIlType<char *>());

	   	   CloseStruct("HeapTupleHeaderData");

	   	   /****Declare HeapTupleData*********/
	   	   OMR::JitBuilder::IlType *HeapTupleDataType = DefineStruct("HeapTupleData");

	   	   DefineField("HeapTupleData", "t_len", Int32);
	   	   DefineField("HeapTupleData", "t_self", ItemPointerDataType);
	   	   DefineField("HeapTupleData", "t_tableOid", Int16);//typedef unsigned int Oid;
	   	   DefineField("HeapTupleData", "t_data", HeapTupleHeaderDataType);
	   	   //DefineField("HeapTupleData", "t_data", pHeapTupleHeaderData, offsetof(t_data, HeapTupleData)+offsetof(t_data, HeapTupleHeader));

	   	   CloseStruct("HeapTupleData");

	   	   //nameDataType
      	   /*OMR::JitBuilder::IlType *nameDataType = DefineStruct("nameData");
      	   DefineField("nameData", "data", d.toIlType<char>());

      	   CloseStruct("nameData");*/

	   	   /*********Declare FormData_pg_attribute***********/
	   	   /*OMR::JitBuilder::IlType *FormData_pg_attributeType = DefineStruct("FormData_pg_attribute");
	   	   OMR::JitBuilder::IlType *pFormData_pg_attributeType = PointerTo("FormData_pg_attribute");


	   	   DefineField("FormData_pg_attribute", "attrelid", Int32);
	   	   DefineField("FormData_pg_attribute", "attname", nameDataType);
	   	   DefineField("FormData_pg_attribute", "atttypid", Int32);
	   	   DefineField("FormData_pg_attribute", "attstattarget", Int32);

	   	   DefineField("FormData_pg_attribute", "attlen", Int16);
	   	   DefineField("FormData_pg_attribute", "attnum", Int16);
	   	   DefineField("FormData_pg_attribute", "attndims", Int32);

	   	   DefineField("FormData_pg_attribute", "attcacheoff", Int32);

	   	   DefineField("FormData_pg_attribute", "atttypmod", Int32);
	   	   DefineField("FormData_pg_attribute", "attbyval", Int32);//bool
	   	   DefineField("FormData_pg_attribute", "attstorage", d.toIlType<char>());
	   	   DefineField("FormData_pg_attribute", "attalign",   d.toIlType<char>());

	   	   DefineField("FormData_pg_attribute", "attnotnull", Int32);
	   	   DefineField("FormData_pg_attribute", "atthasdef", Int32);

	   	   DefineField("FormData_pg_attribute", "atthasmissing", Int32);
	   	   DefineField("FormData_pg_attribute", "attidentity", d.toIlType<char>());
	   	   DefineField("FormData_pg_attribute", "attgenerated", d.toIlType<char>());
	   	   DefineField("FormData_pg_attribute", "attisdropped", Int32);

	   	   DefineField("FormData_pg_attribute", "attislocal", Int32);
	   	   DefineField("FormData_pg_attribute", "attinhcount", Int32);
	   	   DefineField("FormData_pg_attribute", "attcollation", Int32);

	   	   CloseStruct("FormData_pg_attribute");*/

	   	   OMR::JitBuilder::IlType *FormData_pg_attributeType = DEFINE_STRUCT(FormData_pg_attribute);
	   	   OMR::JitBuilder::IlType *pFormData_pg_attributeType = PointerTo("FormData_pg_attribute");


	   	   //DEFINE_FIELD(FormData_pg_attribute, attrelid, Int32);
	   	   //DEFINE_FIELD(FormData_pg_attribute, attname, nameDataType);
	   	   //DEFINE_FIELD(FormData_pg_attribute, atttypid, Int32);
	   	   //DEFINE_FIELD(FormData_pg_attribute, attstattarget, Int32);

	   	   DEFINE_FIELD(FormData_pg_attribute, attlen, Int16);
	   	   //DEFINE_FIELD(FormData_pg_attribute, attnum, Int16);
	   	   //DEFINE_FIELD(FormData_pg_attribute, attndims, Int32);

	   	   DEFINE_FIELD(FormData_pg_attribute, attcacheoff, Int32);

	   	   //DEFINE_FIELD(FormData_pg_attribute, atttypmod, Int32);
	   	   DEFINE_FIELD(FormData_pg_attribute, attbyval, d.toIlType<bool>());//bool
	   	   //DEFINE_FIELD(FormData_pg_attribute, attstorage, d.toIlType<char>());
	   	   DEFINE_FIELD(FormData_pg_attribute, attalign,   d.toIlType<char>());

	   	   //DEFINE_FIELD(FormData_pg_attribute, attnotnull, Int32);
	   	   //DEFINE_FIELD(FormData_pg_attribute, atthasdef, Int32);

	   	   //DEFINE_FIELD(FormData_pg_attribute, atthasmissing, Int32);
	   	   //DEFINE_FIELD(FormData_pg_attribute, attidentity, d.toIlType<char>());
	   	   //DEFINE_FIELD(FormData_pg_attribute, attgenerated, d.toIlType<char>());
	   	   //DEFINE_FIELD(FormData_pg_attribute, attisdropped, Int32);

	   	   //DEFINE_FIELD(FormData_pg_attribute, attislocal, Int32);
	   	   //DEFINE_FIELD(FormData_pg_attribute, attinhcount, Int32);
	   	   //DEFINE_FIELD(FormData_pg_attribute, attcollation, Int32);

	   	   CLOSE_STRUCT(FormData_pg_attribute);

	   	   /*********Declare AttrDefault***********/
	   	   OMR::JitBuilder::IlType *AttrDefaultType = DefineStruct("AttrDefault");
	   	   OMR::JitBuilder::IlType *pAttrDefaultType = PointerTo("AttrDefault");

	   	   DefineField("AttrDefault", "adnum", Int16);
	   	   DefineField("AttrDefault", "adbin", d.toIlType<char *>());

	   	   CLOSE_STRUCT(AttrDefault);

	   	   /*********Declare ConstrCheck***********/
	   	   OMR::JitBuilder::IlType *ConstrCheckType = DefineStruct("ConstrCheck");
	   	   OMR::JitBuilder::IlType *pConstrCheckType = PointerTo("ConstrCheck");

	   	   DefineField("ConstrCheck", "ccname", d.toIlType<char *>());
	   	   DefineField("ConstrCheck", "ccbin", d.toIlType<char *>());
	   	   DefineField("ConstrCheck", "ccvalid", Int32);
	   	   DefineField("ConstrCheck", "ccnoinherit", Int32);

	   	   CloseStruct("ConstrCheck");

	   	   /*********Declare AttrMissing***********/
	   	   OMR::JitBuilder::IlType *AttrMissingType = DefineStruct("AttrMissing");
	   	   OMR::JitBuilder::IlType *pAttrMissingType = PointerTo("AttrMissing");

	   	   DefineField("AttrMissing", "am_present", Int32);
	   	   DefineField("AttrMissing", "am_value", d.toIlType<Datum>());

	   	   CloseStruct("AttrMissing");

	   	   /*********Declare TupleConstr***********/
	   	   /*OMR::JitBuilder::IlType *TupleConstrType = DefineStruct("TupleConstr");
	   	   OMR::JitBuilder::IlType *pTupleConstrType = PointerTo("TupleConstr");

	   	   DefineField("TupleConstr", "defval", pAttrDefaultType);
	   	   DefineField("TupleConstr", "check", pConstrCheckType);
	   	   DefineField("TupleConstr", "missing", pAttrMissingType);
	   	   DefineField("TupleConstr", "num_defval", Int16);
	   	   DefineField("TupleConstr", "num_check", Int16);
	   	   DefineField("TupleConstr", "has_not_null", Int32);
	   	   DefineField("TupleConstr", "has_generated_stored", Int32);

	   	   CloseStruct("TupleConstr");*/

	   	   /*********Declare TupleDescData***********/
	   	   /*OMR::JitBuilder::IlType *TupleDescType = DefineStruct("TupleDescData");

	   	   DefineField("TupleDescData", "natts", Int32);
	   	   DefineField("TupleDescData", "tdtypeid", Int32);
	   	   DefineField("TupleDescData", "tdtypmod", Int32);
	   	   DefineField("TupleDescData", "tdrefcount", Int32);
	   	   DefineField("TupleDescData", "constr", pTupleConstrType);//not sure

	   	   DefineField("TupleDescData", "attrs", pFormData_pg_attributeType);

	   	   CloseStruct("TupleDescData");*/

	   	   OMR::JitBuilder::IlType *TupleDescType = DEFINE_STRUCT(TupleDescData);
	       OMR::JitBuilder::IlType *pTupleDescType = PointerTo("TupleDescData");

	   	   DEFINE_FIELD(TupleDescData, natts, Int32);
	   	   DEFINE_FIELD(TupleDescData, tdtypeid, Int32);
	   	   DEFINE_FIELD(TupleDescData, tdtypmod, Int32);
	   	   DEFINE_FIELD(TupleDescData, tdrefcount, Int32);
	   	   //DEFINE_FIELD(TupleDescData, constr, pTupleConstrType);//not sure

	   	   DEFINE_FIELD(TupleDescData, attrs, pFormData_pg_attributeType/*pInt16*/);

	   	   CLOSE_STRUCT(TupleDescData);

	   	   /*Declare MinimalTupleData*/

	   	   /*OMR::JitBuilder::IlType *MinimalTupleDataType = DefineStruct("MinimalTupleData");
	   	   OMR::JitBuilder::IlType *pMinimalTupleDataType = PointerTo("MinimalTupleData");

	   	   DefineField("MinimalTupleData", "t_len", Int32);
	   	   DefineField("MinimalTupleData", "mt_padding", d.toIlType<char *>());
	   	   DefineField("MinimalTupleData", "t_infomask2", Int16);
	   	   DefineField("MinimalTupleData", "t_infomask", Int16);
	   	   DefineField("MinimalTupleData", "t_hoff", d.toIlType<char>());//not sure
	   	   DefineField("MinimalTupleData", "t_bits", d.toIlType<bits8 *>());

	   	   CloseStruct("MinimalTupleData");*/


	   	   /*Declare TupleTableSlotOps*/

	   	   /*OMR::JitBuilder::IlType *TupleTableSlotOpsType = DefineStruct("TupleTableSlotOps");
	   	   OMR::JitBuilder::IlType *pTupleTableSlotOpsType = PointerTo("TupleTableSlotOps");

	   	   DefineField("TupleTableSlotOps", "base_slot_size", d.toIlType<size_t>());//typedef enum NodeTag
	   	   DefineField("TupleTableSlotOps", "init", NoType);
	   	   DefineField("TupleTableSlotOps", "release", NoType);
	   	   DefineField("TupleTableSlotOps", "clear", NoType);//
	   	   DefineField("TupleTableSlotOps", "getsomeattrs", NoType);
	   	   DefineField("TupleTableSlotOps", "getsysattr", d.toIlType<Datum>());
	   	   DefineField("TupleTableSlotOps", "materialize", NoType);
	   	   DefineField("TupleTableSlotOps", "copyslot", NoType);
	   	   DefineField("TupleTableSlotOps", "get_heap_tuple", HeapTupleDataType);
	   	   DefineField("TupleTableSlotOps", "get_minimal_tuple", MinimalTupleDataType);
	   	   DefineField("TupleTableSlotOps", "copy_heap_tuple", HeapTupleDataType);
	       DefineField("TupleTableSlotOps", "copy_minimal_tuple", MinimalTupleDataType);


	   	   CloseStruct("TupleTableSlotOps");*/

	   	   /****Declare TupleTableSlot*********/
	   	   /*OMR::JitBuilder::IlType *TupleTableSlotType = DefineStruct("TupleTableSlot");

	   	   DefineField("TupleTableSlot", "type", Int16);//typedef enum NodeTag
	   	   DefineField("TupleTableSlot", "tts_flags", Int16);
	   	   DefineField("TupleTableSlot", "tts_nvalid", Int16);
	   	   DefineField("TupleTableSlot", "tts_ops", pTupleTableSlotOpsType);//
	   	   DefineField("TupleTableSlot", "tts_tupleDescriptor", TupleDescType);
	   	   DefineField("TupleTableSlot", "tts_values", d.toIlType<Datum *>());
	   	   DefineField("TupleTableSlot", "tts_isnull", PointerTo(Int32));
	   	   DefineField("TupleTableSlot", "tts_mcxt", Address);//
	   	   DefineField("TupleTableSlot", "tts_tid", ItemPointerDataType);
	   	   DefineField("TupleTableSlot", "tts_tableOid", Int32);


	   	   CloseStruct("TupleTableSlot");*/

	   	   /****Declare TupleTableSlot*********/
	   	   OMR::JitBuilder::IlType *TupleTableSlotType = DEFINE_STRUCT(TupleTableSlot);

	   	   DEFINE_FIELD(TupleTableSlot, tts_flags, Int16);
	   	   DEFINE_FIELD(TupleTableSlot, tts_nvalid, Int16);
	   	   DEFINE_FIELD(TupleTableSlot, tts_tupleDescriptor, /*pInt16*/pTupleDescType);
	   	   DEFINE_FIELD(TupleTableSlot, tts_values, toIlType<Datum *>());
	   	   DEFINE_FIELD(TupleTableSlot, tts_isnull, PointerTo(Int32));

	   	   CLOSE_STRUCT(TupleTableSlot);

      }
   };


OMR::JitBuilder::IlValue*
slot_compile_deform::att_addlength_pointer_cal(IlBuilder *b, OMR::JitBuilder::IlValue *cur_offset, OMR::JitBuilder::IlValue *attlen, OMR::JitBuilder::IlValue *attptr)
{
	b->Store("offset", b->ConstInt32(0));

	OMR::JitBuilder::IlBuilder *attlen_match1 = NULL;
	OMR::JitBuilder::IlBuilder *attlen_match1_else = NULL;

	b->IfThenElse(&attlen_match1, &attlen_match1_else,
	b->   GreaterThan(
    b->      ConvertTo(Int16, attlen),
	b->      ConstInt16(0)));

	//(cur_offset) + (attlen)
	attlen_match1->Store("offset",
	attlen_match1->   Add(
	attlen_match1->      ConvertTo(Int32, attlen),
	                     cur_offset));

	OMR::JitBuilder::IlBuilder *attlen_match2 = NULL;
	OMR::JitBuilder::IlBuilder *attlen_match2_else = NULL;

	attlen_match1_else->IfThenElse(&attlen_match2, &attlen_match2_else,
	attlen_match1_else->   EqualTo(
	attlen_match1_else->      ConvertTo(Int16, attlen),
	attlen_match1_else->      ConstInt16(-1)));

	//(cur_offset) + VARSIZE_ANY(attptr)
	attlen_match2->Store("offset",
	attlen_match2->Add(
	attlen_match2->   ConvertTo(Int32, cur_offset),
	attlen_match2->   ConvertTo(Int32, attlen_match2->Call("VARSIZE_ANY_func", 1,
	attlen_match2->      ConvertTo(pStr, attptr)))));

	//(cur_offset) + (strlen((char *) (attptr)) + 1)
	attlen_match2_else->Store("offset",
    attlen_match2_else->   Add(
	attlen_match2_else->      ConvertTo(Int32, cur_offset),
	attlen_match2_else->      Add(
	attlen_match2_else->         ConstInt32(1),
	attlen_match2_else->         ConvertTo(Int32, attlen_match2_else->Call("strlen_func",1,
    attlen_match2_else->            ConvertTo(pStr, attptr)))))     );

	return b->Load("offset");

}

OMR::JitBuilder::IlValue*
slot_compile_deform::att_align_nominal_cal(IlBuilder *b, OMR::JitBuilder::IlValue *cur_offset, OMR::JitBuilder::IlValue *attalign)
{

	//OMR::JitBuilder::IlValue *off = b->ConstInt32(0);
	b->Store("cal_off", b->ConstInt32(0));

	OMR::JitBuilder::IlBuilder *TYPALIGN_INT_match = NULL;
	OMR::JitBuilder::IlBuilder *TYPALIGN_INT_match_else = NULL;

	//if
	b->IfThenElse(&TYPALIGN_INT_match, &TYPALIGN_INT_match_else,
    b->   EqualTo(
	b->      ConvertTo(Int16,attalign),
	b->      ConstInt16(TYPALIGN_INT)));

	//#define INTALIGN(LEN)	  TYPEALIGN(ALIGNOF_INT, (LEN))
	//#define TYPEALIGN(ALIGNVAL,LEN)
	//   (((uintptr_t) (LEN) + ((ALIGNVAL) - 1)) & ~((uintptr_t) ((ALIGNVAL) - 1))) = (((uintptr_t) (LEN) + 3) & ~((uintptr_t) 3))
	TYPALIGN_INT_match->Store("cal_off",
	TYPALIGN_INT_match->ConvertTo(Int32,
    TYPALIGN_INT_match->And(
    TYPALIGN_INT_match->   Add( TYPALIGN_INT_match->ConvertTo(Int32, cur_offset),
	TYPALIGN_INT_match->      ConstInt32(3)),
    TYPALIGN_INT_match->   ConstInt32(~3)))    );
	//TYPALIGN_INT_match->Call("print_func", 2, cur_offset, TYPALIGN_INT_match->ConvertTo(Int32, TYPALIGN_INT_match->Load("cal_off")));

    //else
	OMR::JitBuilder::IlBuilder *TYPALIGN_CHAR_match = NULL;
	OMR::JitBuilder::IlBuilder *TYPALIGN_CHAR_match_else = NULL;

	//if
	//(((attalign) == TYPALIGN_CHAR) ?
	TYPALIGN_INT_match_else->IfThenElse(&TYPALIGN_CHAR_match, &TYPALIGN_CHAR_match_else,
	TYPALIGN_INT_match_else->   EqualTo(
    TYPALIGN_INT_match_else->      ConvertTo(Int16,attalign),
    TYPALIGN_INT_match_else->      ConstInt16(TYPALIGN_CHAR)));

	//(uintptr_t) (cur_offset)
	TYPALIGN_CHAR_match->Store("cal_off",
    TYPALIGN_CHAR_match->ConvertTo(Int32, cur_offset));
	//TYPALIGN_CHAR_match->Call("print_func", 2, cur_offset, TYPALIGN_CHAR_match->ConvertTo(Int32, off));

    //else
	OMR::JitBuilder::IlBuilder *TYPALIGN_DOUBLE_match = NULL;
	OMR::JitBuilder::IlBuilder *TYPALIGN_DOUBLE_match_else = NULL;

	//if
	//(((attalign) == TYPALIGN_DOUBLE) ?
	TYPALIGN_CHAR_match_else->IfThenElse(&TYPALIGN_DOUBLE_match, &TYPALIGN_DOUBLE_match_else,
    TYPALIGN_CHAR_match_else->   EqualTo(
	TYPALIGN_CHAR_match_else->      ConvertTo(Int16,attalign),
    TYPALIGN_CHAR_match_else->      ConstInt16(TYPALIGN_DOUBLE)));

	//#define DOUBLEALIGN(LEN)	  TYPEALIGN(ALIGNOF_DOUBLE, (LEN))
	//#define TYPEALIGN(ALIGNVAL,LEN)
	//   (((uintptr_t) (LEN) + ((ALIGNVAL) - 1)) & ~((uintptr_t) ((ALIGNVAL) - 1))) = (((uintptr_t) (LEN) + 7) & ~((uintptr_t) 7))
	TYPALIGN_DOUBLE_match->Store("cal_off",
    TYPALIGN_DOUBLE_match->ConvertTo(Int32,
    TYPALIGN_DOUBLE_match->And(
	TYPALIGN_DOUBLE_match->   Add(TYPALIGN_DOUBLE_match->ConvertTo(Int32, cur_offset),
	TYPALIGN_DOUBLE_match->      ConstInt32(7)),
	TYPALIGN_DOUBLE_match->      ConstInt32(~7)))    );
	//TYPALIGN_DOUBLE_match->Call("print_func", 2, cur_offset, TYPALIGN_DOUBLE_match->ConvertTo(Int32, off));

	//else

	//#define SHORTALIGN(LEN)	TYPEALIGN(ALIGNOF_SHORT, (LEN))
	//#define TYPEALIGN(ALIGNVAL,LEN)
	//   (((uintptr_t) (LEN) + ((ALIGNVAL) - 1)) & ~((uintptr_t) ((ALIGNVAL) - 1))) = (((uintptr_t) (LEN) + 1) & ~((uintptr_t) 1))
	TYPALIGN_DOUBLE_match_else->Store("cal_off",
	TYPALIGN_DOUBLE_match_else->ConvertTo(Int32,
	TYPALIGN_DOUBLE_match_else->And(
	TYPALIGN_DOUBLE_match_else->   Add(TYPALIGN_DOUBLE_match_else->ConvertTo(Int32, cur_offset),
	TYPALIGN_DOUBLE_match_else->      ConstInt32(1)),
	TYPALIGN_DOUBLE_match_else->      ConstInt32(~1)))   );

	//TYPALIGN_DOUBLE_match_else->Call("print_func", 2, cur_offset, TYPALIGN_DOUBLE_match_else->ConvertTo(Int32, off));

	//b->Call("print_func", 2, b->ConstInt32(0), b->ConvertTo(Int32, b->Load("cal_off")));
	//Return (off);
	return b->Load("cal_off");

}

OMR::JitBuilder::IlValue*
slot_compile_deform::att_align_pointer_cal(IlBuilder *b, OMR::JitBuilder::IlValue *cur_offset, OMR::JitBuilder::IlValue *attalign,
		OMR::JitBuilder::IlValue *attlen, OMR::JitBuilder::IlValue *attptr)
{
	b->Store("off_align_ptr", b->ConstInt32(0));

	b->Store("off_align_ptr_flag", b->ConstInt32(0));

	OMR::JitBuilder::IlBuilder *attlen_align_pointer_match = NULL;

	b->IfThen(&attlen_align_pointer_match,
    b->   EqualTo(
    b->      ConvertTo(Int32, attlen),
	b->      ConstInt32(-1)));

	//Translation for: (*((uint8 *) (PTR)) != 0)
	OMR::JitBuilder::IlBuilder *VARATT_NOT_PAD_BYTE_match = NULL;
	attlen_align_pointer_match->IfThen(&VARATT_NOT_PAD_BYTE_match,
    attlen_align_pointer_match->   NotEqualTo(
    attlen_align_pointer_match->      ConvertTo(Int32,
    attlen_align_pointer_match->         Call("t_uint32_func", 1,
    attlen_align_pointer_match->		    ConvertTo(pStr, attptr))),
	attlen_align_pointer_match->      ConstInt32(0)));

	//Translation for: uintptr_t) (cur_offset)
	VARATT_NOT_PAD_BYTE_match->Store("off_align_ptr",
	VARATT_NOT_PAD_BYTE_match->   ConvertTo(Int32, cur_offset));

	//set the flag
	VARATT_NOT_PAD_BYTE_match->Store("off_align_ptr_flag",
    VARATT_NOT_PAD_BYTE_match->   ConstInt32(1));

	OMR::JitBuilder::IlBuilder *off_align_ptr_flag_match = NULL;

	b->IfThen(&off_align_ptr_flag_match,
	b->   EqualTo(
	b->      Load("off_align_ptr_flag"),
	b->      ConstInt32(0)));

	off_align_ptr_flag_match->Store("off_align_ptr",
	off_align_ptr_flag_match->ConvertTo(Int32, att_align_nominal_cal(off_align_ptr_flag_match, cur_offset, attalign)   ));


    return b->Load("off_align_ptr");


}

OMR::JitBuilder::IlValue*
slot_compile_deform::fetch_attributes(IlBuilder *b, OMR::JitBuilder::IlValue *thisatt, OMR::JitBuilder::IlValue *tp, OMR::JitBuilder::IlValue *offset)
{

	b->Store("att", b->ConvertTo(Address, b->ConstInt32(0)));

	b->Store("attlen",
    b->   ConvertTo(Int16,
    b->      LoadIndirect("FormData_pg_attribute", "attlen",thisatt)));

	b->Store("attbyval",
    b->   ConvertTo(Int16, b->LoadIndirect("FormData_pg_attribute", "attbyval", thisatt)));


	 // (int) sizeof(Datum) = 8
	 // (int) sizeof(int32) = 4
	 // (int) sizeof(int16) = 2


    // For byval: datums copy the value, extend to Datum's width, and store.
	//b->Call("print_func", 1, b->ConstInt16(TYPALIGN_INT));
    OMR::JitBuilder::IlBuilder *attbyval_match = NULL;
    OMR::JitBuilder::IlBuilder *attbyval_match_else = NULL;

    //If byval true
    b->IfThenElse(&attbyval_match, &attbyval_match_else,
    b->   EqualTo(
    b->      Load("attbyval"),
	b->      ConstInt16(1)));

    //------------------By Value--------------------------

    //Translation for:  (attlen) == (int) sizeof(Datum) ?
    OMR::JitBuilder::IlBuilder *attlenDat_match = NULL;
    OMR::JitBuilder::IlBuilder *attlenDat_match_else = NULL;

    //if of datum
    attbyval_match->IfThenElse(&attlenDat_match, &attlenDat_match_else,
    attbyval_match->   EqualTo(
    attbyval_match->      Load("attlen"),
    attbyval_match->      ConstInt16((int) sizeof(Datum))));

    //Translation for:  *((Datum *)(T))
    //attlenDat_match->Store("att", /*attlenDat_match->ConvertTo(datum_rep, */attlenDat_match->ConvertTo(pDatum, attlenDat_match->ConvertTo(pStr, tp)));
    attlenDat_match->Store("att", attlenDat_match->Call("t_datum_func",1, attlenDat_match->ConvertTo(pStr, tp)));

    //else of datum
    //Check for Int32 representation i.e (attlen) == (int) sizeof(int32) ?
    OMR::JitBuilder::IlBuilder *attlenInt32_match = NULL;
    OMR::JitBuilder::IlBuilder *attlenInt32_match_else = NULL;

    //if int32
    attlenDat_match_else->IfThenElse(&attlenInt32_match, &attlenInt32_match_else,
    attlenDat_match_else->   EqualTo(
    attlenDat_match_else->      Load("attlen"),
    attlenDat_match_else->      ConstInt16((int) sizeof(int32))));

    //Translation for: Int32GetDatum(*((int32 *)(T)))
    //attlenInt32_match->Store("att", attlenInt32_match->ConvertTo(Address, /*attlenInt32_match->ConvertTo(int32_rep, */attlenInt32_match->ConvertTo(pInt32, attlenInt32_match->ConvertTo(pStr, tp))));
    attlenInt32_match->Store("att", attlenInt32_match->ConvertTo(Address, attlenInt32_match->Call("t_int32_func",1, attlenInt32_match->ConvertTo(pStr, tp))));

    //else of Int32
    OMR::JitBuilder::IlBuilder *attlenInt16_match = NULL;
    OMR::JitBuilder::IlBuilder *attlenInt16_match_else = NULL;

    //if int16
    attlenInt32_match_else->IfThenElse(&attlenInt16_match, &attlenInt16_match_else,
    attlenInt32_match_else->   EqualTo(
    attlenInt32_match_else->      Load("attlen"),
	attlenInt32_match_else->      ConstInt16((int) sizeof(int16))));

    //Translation for: Int16GetDatum(*((int16 *)(T)))
    //attlenInt16_match->Store("att", attlenInt16_match->ConvertTo(Address, /*attlenInt16_match->ConvertTo(int16_rep,*/ attlenInt16_match->ConvertTo(pInt16, attlenInt16_match->ConvertTo(pStr, tp))));
    attlenInt16_match->Store("att", attlenInt16_match->ConvertTo(Address, attlenInt16_match->Call("t_int16_func",1, attlenInt16_match->ConvertTo(pStr, tp))));

    //else of Int16
    //translation for: CharGetDatum(*((char *)(T)))
    //attlenInt16_match_else->Store("att", attlenInt16_match_else->ConvertTo(Address, /*attlenInt16_match_else->ConvertTo(str_rep, */attlenInt16_match_else->ConvertTo(pStr, attlenInt16_match_else->ConvertTo(pStr, tp))));
    attlenInt16_match_else->Store("att", attlenInt16_match_else->ConvertTo(Address, attlenInt16_match_else->Call("t_str_func",1, attlenInt16_match_else->ConvertTo(pStr, tp))));


    ///------------------By Reference--------------------------
    //For byref types: store pointer to data.
    //Translation for: PointerGetDatum((char *) (T))
    attbyval_match_else->Store("att", attbyval_match_else->ConvertTo(Address, attbyval_match_else->ConvertTo(pStr, tp)));

	return b->Load("att");


}


/******************************BUILDIL**********************************************/

bool
slot_compile_deform::buildIL()
   {
   /* Runtime c-function to compute the whole tuple deformation */

   //slot_deform_heap_tuple(slot, bslot->base.tuple, &bslot->base.off, natts);
   //Call("slot_deform_heap_tuple", 4, Load("slot"), Load("tuple"), Load("offp"), Load("natts"));


   /*************************Convert the interpreted model**************************************/

   //Load natts
   Store("load_natts", ConvertTo(Int16, Load("natts")));
   //TupleDesc	tupleDesc = slot->tts_tupleDescriptor;
   Store("tupleDesc",
	  LoadIndirect("TupleTableSlot","tts_tupleDescriptor",
		 Load("slot")));

   //bool	   *isnull = slot->tts_isnull;

   //HeapTupleHeader tup = tuple->t_data;
   Store("tup",
      LoadIndirect("HeapTupleData", "t_data",
	     Load("tuple")));

   //bool hasnulls = HeapTupleHasNulls(tuple);  (((tuple)->t_data->t_infomask & 0x0001) != 0)
   Store("hasnulls", ConstInt32(0));

   OMR::JitBuilder::IlBuilder *nulls_check = NULL;
   IfThen(&nulls_check,
      NotEqualTo(
         And(
            ConstInt16(1),
        	LoadIndirect("HeapTupleHeaderData", "t_infomask",
        	   Load("tup"))),
		 ConstInt16(0)));

   nulls_check->Store("hasnulls",
   nulls_check->   ConstInt32(1));

   //int attnum = slot->tts_nvalid;
   Store("attnum",
      ConvertTo(Int16, LoadIndirect("TupleTableSlot", "tts_nvalid",
         Load("slot"))));

   /*Earlier jitted this operation, but is error prone so used runtime c-function*/
   //char *tp = (char *) tup + tup->t_hoff;
   /*Store("tp",
      Add(
         Load("tup"),
		 ConvertTo(Word,
		    LoadIndirect("HeapTupleHeaderData", "t_hoff",
               Load("tup"))))  );*/
   Store("tp1",
      Call("tp_func", 1,
         Load("tup")));

   //uint32	off;
   Store("off",
      ConstInt32(0));


   //bits8 *bp = tup->t_bits;

   //bool slow;
   Store("slow",
      ConstInt32(0));

   //natts = Min(HeapTupleHeaderGetNatts(tuple->t_data), natts);
   Store("HeapTupleHeaderGetNatts",
      And(
         LoadIndirect("HeapTupleHeaderData", "t_infomask2",
            Load("tup")),
	     ConstInt16(HEAP_NATTS_MASK)));//HEAP_NATTS_MASK = 2047

   //find the min
   OMR::JitBuilder::IlBuilder *natts_min_match = NULL;
   IfThen(&natts_min_match,
      LessThan(
         Load("HeapTupleHeaderGetNatts"),
		 ConvertTo(Int16, Load("natts"))));

   natts_min_match->Store("load_natts",
   natts_min_match->    ConvertTo(Int16,Load("HeapTupleHeaderGetNatts")));

   //only store is != that is if (attnum != 0), because we have already set slow and off for the case attnum == 0)
   OMR::JitBuilder::IlBuilder *attnum_match = NULL;
   IfThen(&attnum_match,
      NotEqualTo(
         Load("attnum"),
		 ConstInt16(0)));

   //off = *offp;
   attnum_match->Store("off",
   attnum_match->   LoadAt(pInt32,
   attnum_match->      Load("offp")));

   //slow = TTS_SLOW(slot); (((slot)->tts_flags & (1 << 3)) != 0)
   attnum_match->Store("slow",
   attnum_match->   NotEqualTo(
   attnum_match->     And(
   attnum_match->        LoadIndirect("TupleTableSlot", "tts_flags",
   attnum_match->          Load("slot")),
   attnum_match->		ConstInt16(8)),
   attnum_match->	 ConstInt16(0)));

   Store("slow_test", Load("offp"));


   //Store("attnum_val", ConstInt16(0));
   //for (; attnum < natts; attnum++)
   OMR::JitBuilder::IlBuilder* attnum_loop = NULL;
   ForLoopUp("attnum_index", &attnum_loop,
	  ConvertTo(Int32, Load("attnum")),
	  ConvertTo(Int32, Load("load_natts")),
      ConstInt32(1));

   //print current offset
   //attnum_loop->Call("print_func", 1, attnum_loop->Load("off"));

   //Form_pg_attribute thisatt = TupleDescAttr(tupleDesc, attnum);
   attnum_loop->Store("thisatt",
   attnum_loop->   IndexAt(pFormData_pg_attribute,
   attnum_loop->      StructFieldInstanceAddress("TupleDescData", "attrs",
   attnum_loop->         Load("tupleDesc")),
   attnum_loop->       Load("attnum_index"))            );


   OMR::JitBuilder::IlBuilder *hasnulls_att_isnull_match = NULL;

   //if (hasnulls)
   attnum_loop->Store("continue_flag",
   attnum_loop->   ConstInt32(0));

   attnum_loop->IfThen(&hasnulls_att_isnull_match,
   attnum_loop->   EqualTo(
   attnum_loop->      Load("hasnulls"),
   attnum_loop->      ConstInt32(1)));

   //if(att_isnull(attnum, bp))
   OMR::JitBuilder::IlBuilder *att_isnull_Match = NULL;
   //OMR::JitBuilder::IlBuilder *att_isnull_else = NULL;

   //att_isnull(ATT, BITS) (!((BITS)[(ATT) >> 3] & (1 << ((ATT) & 0x07))))
   hasnulls_att_isnull_match->IfThen(&att_isnull_Match,
   hasnulls_att_isnull_match->   NotEqualTo(
   hasnulls_att_isnull_match->      And(
   hasnulls_att_isnull_match->         ConvertTo(Int32, LoadAt(pStr,
   hasnulls_att_isnull_match->            IndexAt(pStr,
   hasnulls_att_isnull_match->               LoadIndirect("HeapTupleHeaderData", "t_bits",
   hasnulls_att_isnull_match->                  Load("tup")),
   hasnulls_att_isnull_match->                ShiftR(
   hasnulls_att_isnull_match->                   ConvertTo(Int32,hasnulls_att_isnull_match->Load("attnum_index")),
   hasnulls_att_isnull_match->                   ConstInt32(3))))),
   hasnulls_att_isnull_match->         ShiftL(
   hasnulls_att_isnull_match->            ConstInt32(1),
   hasnulls_att_isnull_match->            And(
   hasnulls_att_isnull_match->               Load("attnum_index"),
   hasnulls_att_isnull_match->               ConstInt32(7)))),
   hasnulls_att_isnull_match->      ConstInt32(0)));

   //values[attnum] = (Datum) 0;
   att_isnull_Match->StoreAt(
   att_isnull_Match->   IndexAt(pDatum,
   att_isnull_Match->      LoadIndirect("TupleTableSlot", "tts_values",
   att_isnull_Match->         Load("slot")),
   att_isnull_Match->      Load("attnum_index")),
   att_isnull_Match->   ConvertTo(Address,
   att_isnull_Match->      ConstInt32(0)));


   //isnull[attnum] = true;
   att_isnull_Match->StoreAt(
   att_isnull_Match->   IndexAt(pInt32,
   att_isnull_Match->      LoadIndirect("TupleTableSlot", "tts_isnull",
   att_isnull_Match->         Load("slot")),
   att_isnull_Match->      Load("attnum_index")),
   att_isnull_Match->   ConstInt32(1));

   //slow = true;
   att_isnull_Match->Store("slow",
   att_isnull_Match->   ConstInt32(1));

   att_isnull_Match->Store("continue_flag",
   att_isnull_Match->   ConstInt32(1));

   att_isnull_Match->Store("attnum",
   att_isnull_Match->   Add(
   att_isnull_Match->      Load("attnum"),
   att_isnull_Match->      ConstInt16(1)));

   //-----------Updated if and continue implementation--------------
   OMR::JitBuilder::IlBuilder *att_isnull_Match_else = NULL;

   attnum_loop->IfThen(&att_isnull_Match_else,
   attnum_loop->   EqualTo(
   attnum_loop->      Load("continue_flag"),
   attnum_loop->      ConstInt32(0)));


   //-------------continue------------------

   //isnull[attnum] = false;
   att_isnull_Match_else->StoreAt(
   att_isnull_Match_else->   IndexAt(pInt32,
   att_isnull_Match_else->      LoadIndirect("TupleTableSlot", "tts_isnull",
   att_isnull_Match_else->         Load("slot")),
   att_isnull_Match_else->      Load("attnum_index")),
   att_isnull_Match_else->   ConstInt32(0));


   //----------------------------------------------------------implement the if, else if, else statements-----------------------------------------------------//

   /*Implement the "c-if" condition in the "OMR if-condition" and implement the "c-else", "c-else-if" inside the "OMR else-condition"*/

   //Set slow_attcacheoff_flag to 0, which guesses if the "else-if, else" conditions needed to be implemented.
   //It is changed to 1 only when if (!slow && thisatt->attcacheoff >= 0) is true

   att_isnull_Match_else->Store("slow_attcacheoff_flag",
   att_isnull_Match_else->   ConstInt32(0));

   //Implementing the "if" i.e if(!slow )
   OMR::JitBuilder::IlBuilder *slow_attcacheoff_match1 = NULL;

   att_isnull_Match_else->IfThen(&slow_attcacheoff_match1,
   att_isnull_Match_else->   LessThan(
   att_isnull_Match_else->      Load("slow"),
   att_isnull_Match_else->      ConstInt32(1)));

   //if( !slow && thisatt->attcacheoff >= 0), it happens only when if(!slow) is true in the previous if
   OMR::JitBuilder::IlBuilder *slow_attcacheoff_match2 = NULL;
   //OMR::JitBuilder::IlBuilder *slow_attcacheoff_match2_else = NULL;

   slow_attcacheoff_match1->IfThen(&slow_attcacheoff_match2,
   slow_attcacheoff_match1->   GreaterOrEqualTo(
   slow_attcacheoff_match1->      LoadIndirect("FormData_pg_attribute", "attcacheoff",
   slow_attcacheoff_match1->         Load("thisatt")),
   slow_attcacheoff_match1->      ConstInt32(0)));

   //off = thisatt->attcacheoff;
   slow_attcacheoff_match2->Store("off",
   slow_attcacheoff_match2->   ConvertTo(Int32,
   slow_attcacheoff_match2->      LoadIndirect("FormData_pg_attribute", "attcacheoff",
   slow_attcacheoff_match2->         Load("thisatt"))));

   //set slow_attcacheoff_flag=1 so that we don't compute any else-if and else statements
   slow_attcacheoff_match2->Store("slow_attcacheoff_flag",
   slow_attcacheoff_match2->   ConstInt32(1));

   //check slow_attcacheoff_flag == 0 ,
   //by which we determine if any 1 of the above if statements return false so that we have to compute the else-if/else part of the if-statement
   //This is essentially a if statement in OMRJIT which evaluates if(slow_attcacheoff_flag_match == 0) so that the else-if/else part needs to be computed
   OMR::JitBuilder::IlBuilder *slow_attcacheoff_flag_match = NULL;

   att_isnull_Match_else->IfThen(&slow_attcacheoff_flag_match,
   att_isnull_Match_else->   EqualTo(
   att_isnull_Match_else->      Load("slow_attcacheoff_flag"),
   att_isnull_Match_else->      ConstInt32(0)));

   //-------Implementing the "else" i.e if (slow == true) OR (thisatt->attcacheoff < 0) OR BOTH------

   //This must be another if-else statement within the else part slow_attcacheoff_match2_else

   OMR::JitBuilder::IlBuilder *thisatt_attlen_negative_match = NULL;
   OMR::JitBuilder::IlBuilder *thisatt_attlen_negative_match_else = NULL;

   //check if (thisatt->attlen == -1)

   slow_attcacheoff_flag_match->IfThenElse(&thisatt_attlen_negative_match, &thisatt_attlen_negative_match_else,
   slow_attcacheoff_flag_match->   EqualTo(
   slow_attcacheoff_flag_match->      ConvertTo(Int32,
   slow_attcacheoff_flag_match->         LoadIndirect("FormData_pg_attribute", "attlen",
   slow_attcacheoff_flag_match->            Load("thisatt"))),
   slow_attcacheoff_flag_match->      ConstInt32(-1)));


   //implement the if part of thisatt_attlen_negative_match

   //set slow_thisatt_attlen_negative_match_flag, which help determine if the else part of if (!slow && off == att_align_nominal(off, thisatt->attalign))
   //has to be executed
   thisatt_attlen_negative_match->Store("slow_thisatt_attlen_negative_match_flag",
   thisatt_attlen_negative_match->   ConstInt32(0));
   //if (!slow)
   OMR::JitBuilder::IlBuilder *slow_thisatt_attlen_negative_match = NULL;

   thisatt_attlen_negative_match->IfThen(&slow_thisatt_attlen_negative_match,
   thisatt_attlen_negative_match->   LessThan(
   thisatt_attlen_negative_match->      Load("slow"),
   thisatt_attlen_negative_match->      ConstInt32(1)));

   //And if(off == att_align_nominal(off, thisatt->attalign))
   OMR::JitBuilder::IlBuilder *slow_off_att_align_nominal_match = NULL;
   //OMR::JitBuilder::IlBuilder *slow_off_att_align_nominal_match_else = NULL;

   /*slow_thisatt_attlen_negative_match->IfThen(&slow_off_att_align_nominal_match,
   slow_thisatt_attlen_negative_match->   EqualTo(
   slow_thisatt_attlen_negative_match->      Load("off"),
   slow_thisatt_attlen_negative_match->      ConvertTo(Int32,
   slow_thisatt_attlen_negative_match->         Call("att_align_nominal_func", 2,
   slow_thisatt_attlen_negative_match->            Load("off"),
   slow_thisatt_attlen_negative_match->            LoadIndirect("FormData_pg_attribute", "attalign",
   slow_thisatt_attlen_negative_match->               Load("thisatt"))))));*/
   //att_align_nominal_cal
   slow_thisatt_attlen_negative_match->IfThen(&slow_off_att_align_nominal_match,
   slow_thisatt_attlen_negative_match->   EqualTo(
   slow_thisatt_attlen_negative_match->      Load("off"),

   slow_thisatt_attlen_negative_match->ConvertTo(Int32, att_align_nominal_cal(                 slow_thisatt_attlen_negative_match,
   slow_thisatt_attlen_negative_match->   Load("off"),
   slow_thisatt_attlen_negative_match->   LoadIndirect("FormData_pg_attribute", "attalign",
   slow_thisatt_attlen_negative_match->      Load("thisatt"))))     ));


   //thisatt->attcacheoff = off;
   slow_off_att_align_nominal_match->StoreIndirect("FormData_pg_attribute", "attcacheoff",
   slow_off_att_align_nominal_match->   Load("thisatt"),
   slow_off_att_align_nominal_match->   ConvertTo(Int32,
   slow_off_att_align_nominal_match->      Load("off")));

   //set slow_thisatt_attlen_negative_match_flag = 1 so that the else need not to be computed
   slow_off_att_align_nominal_match->Store("slow_thisatt_attlen_negative_match_flag",
   slow_off_att_align_nominal_match->   ConstInt32(1));


   //else if either if(slow) OR if(off == att_align_nominal(off, thisatt->attalign))
   //check if slow_thisatt_attlen_negative_match_flag == 0 i.e if statement doesn't hold true

   OMR::JitBuilder::IlBuilder *slow_off_att_align_nominal_match_else = NULL;
   thisatt_attlen_negative_match->IfThen(&slow_off_att_align_nominal_match_else,
   thisatt_attlen_negative_match->   EqualTo(
   thisatt_attlen_negative_match->      Load("slow_thisatt_attlen_negative_match_flag"),
   thisatt_attlen_negative_match->      ConstInt32(0)));

   //off = att_align_pointer(off, thisatt->attalign, -1, tp + off);
   /*slow_off_att_align_nominal_match_else->Store("off",
   slow_off_att_align_nominal_match_else->   ConvertTo(Int32,
   slow_off_att_align_nominal_match_else->      Call("att_align_pointer_func", 4,
   slow_off_att_align_nominal_match_else->         Load("off"),
   slow_off_att_align_nominal_match_else->         LoadIndirect("FormData_pg_attribute", "attalign",
   slow_off_att_align_nominal_match_else->            Load("thisatt")),
   slow_off_att_align_nominal_match_else->         ConstInt32(-1),
   slow_off_att_align_nominal_match_else->         Add(
   slow_off_att_align_nominal_match_else->            Load("tp1"),
   slow_off_att_align_nominal_match_else->            Load("off"))   )));*/

   //att_align_pointer_cal
   slow_off_att_align_nominal_match_else->Store("off",
   slow_off_att_align_nominal_match_else->   ConvertTo(Int32,
   att_align_pointer_cal(slow_off_att_align_nominal_match_else,
   slow_off_att_align_nominal_match_else->         Load("off"),
   slow_off_att_align_nominal_match_else->         LoadIndirect("FormData_pg_attribute", "attalign",
   slow_off_att_align_nominal_match_else->            Load("thisatt")),
   slow_off_att_align_nominal_match_else->         ConstInt32(-1),
   slow_off_att_align_nominal_match_else->         Add(
   slow_off_att_align_nominal_match_else->            Load("tp1"),
   slow_off_att_align_nominal_match_else->            Load("off"))   )));

   //slow = true;
   slow_off_att_align_nominal_match_else->Store("slow",
   slow_off_att_align_nominal_match_else->   ConstInt32(1));

   //implement the else part of if (thisatt->attlen == -1) i.e  thisatt_attlen_negative_match_else

   //off = att_align_nominal(off, thisatt->attalign);
   /*thisatt_attlen_negative_match_else->Store("off",
   thisatt_attlen_negative_match_else->   ConvertTo(Int32,
   thisatt_attlen_negative_match_else->      Call("att_align_nominal_func", 2,
   thisatt_attlen_negative_match_else->         Load("off"),
   thisatt_attlen_negative_match_else->         LoadIndirect("FormData_pg_attribute", "attalign",
   thisatt_attlen_negative_match_else->            Load("thisatt")))));*/

   //att_align_nominal_cal
   thisatt_attlen_negative_match_else->Store("off",
   thisatt_attlen_negative_match_else->   ConvertTo(Int32,att_align_nominal_cal(                 thisatt_attlen_negative_match_else,
   thisatt_attlen_negative_match_else->   Load("off"),
   thisatt_attlen_negative_match_else->   LoadIndirect("FormData_pg_attribute", "attalign",
   thisatt_attlen_negative_match_else->      Load("thisatt")))));

   //if (!slow)
   OMR::JitBuilder::IlBuilder *slow_thisatt_attlen_negative_match_else = NULL;

   thisatt_attlen_negative_match_else->IfThen(&slow_thisatt_attlen_negative_match_else,
   thisatt_attlen_negative_match_else->   LessThan(
   thisatt_attlen_negative_match_else->      Load("slow"),
   thisatt_attlen_negative_match_else->      ConstInt32(1)));

   //thisatt->attcacheoff = off;
   slow_thisatt_attlen_negative_match_else->StoreIndirect("FormData_pg_attribute", "attcacheoff",
   slow_thisatt_attlen_negative_match_else->   Load("thisatt"),
   slow_thisatt_attlen_negative_match_else->   ConvertTo(Int32,
   slow_thisatt_attlen_negative_match_else->      Load("off")));

   //---------------------------------------------------All of if,else,else-if is COMPLETE------------------------------------------------------------//

   att_isnull_Match_else->Store("attnum",
   att_isnull_Match_else->   Add(
   att_isnull_Match_else->      Load("attnum"),
   att_isnull_Match_else->      ConstInt16(1)));


   //------- when the if, else if, else statements DONE--------

   //values[attnum] = fetchatt(thisatt, tp + off);

   /*att_isnull_Match_else->StoreAt(
   att_isnull_Match_else->   IndexAt(pDatum,
   att_isnull_Match_else->      LoadIndirect("TupleTableSlot", "tts_values",
   att_isnull_Match_else->         Load("slot")),
   att_isnull_Match_else->      Load("attnum_index")),
   att_isnull_Match_else->      ConvertTo(Address,
   att_isnull_Match_else->         Call("fetchatt_func", 3,
   att_isnull_Match_else->            Load("thisatt"),
   att_isnull_Match_else->            Add(
   att_isnull_Match_else->               Load("tp1"),
   att_isnull_Match_else->				 Load("off")),
   att_isnull_Match_else->            Load("off"))));//Store fetchatt(thisatt, tp + off)*/

   //fetchatt_func now Jitted, but the pointer casting is still computed using runtime c-function
   att_isnull_Match_else->StoreAt(
   att_isnull_Match_else->   IndexAt(pDatum,
   att_isnull_Match_else->      LoadIndirect("TupleTableSlot", "tts_values",
   att_isnull_Match_else->         Load("slot")),
   att_isnull_Match_else->      Load("attnum_index")),
   att_isnull_Match_else->ConvertTo(Address,fetch_attributes(         att_isnull_Match_else,
   att_isnull_Match_else->   Load("thisatt"),
   att_isnull_Match_else->   Add(
   att_isnull_Match_else->      Load("tp1"),
   att_isnull_Match_else->      Load("off")),
   att_isnull_Match_else->   Load("off"))));

   /* att_addlength_pointer_func was previously computed as runtime c-function */

   //off = att_addlength_pointer(off, thisatt->attlen, tp + off);
   /*att_isnull_Match_else->Store("off",
   att_isnull_Match_else->   ConvertTo(Int32,
   att_isnull_Match_else->      Call("att_addlength_pointer_func", 3,
   att_isnull_Match_else->         Load("off"),
   att_isnull_Match_else->         LoadIndirect("FormData_pg_attribute", "attlen",
   att_isnull_Match_else->            Load("thisatt")),
   att_isnull_Match_else->         Add(
   att_isnull_Match_else->            Load("tp1"),
   att_isnull_Match_else->            Load("off"))          )));*/

   //att_addlength_pointer_cal now Jitted
   att_isnull_Match_else->Store("off",
   att_isnull_Match_else->   ConvertTo(Int32,
   att_addlength_pointer_cal(      att_isnull_Match_else,
   att_isnull_Match_else->         Load("off"),
   att_isnull_Match_else->         LoadIndirect("FormData_pg_attribute", "attlen",
   att_isnull_Match_else->            Load("thisatt")),
   att_isnull_Match_else->         Add(
   att_isnull_Match_else->            Load("tp1"),
   att_isnull_Match_else->            Load("off"))          )));

   //if (thisatt->attlen <= 0)
   OMR::JitBuilder::IlBuilder *thisatt_attlen_match = NULL;
   IfThen(&thisatt_attlen_match,
   att_isnull_Match_else->   LessOrEqualTo(
   att_isnull_Match_else->      LoadIndirect("FormData_pg_attribute", "attlen",
   att_isnull_Match_else->         Load("thisatt")),
   att_isnull_Match_else->      ConstInt16(0)));

   //slow = true;
   thisatt_attlen_match->Store("slow",
   thisatt_attlen_match->   ConstInt32(1));


   //Save state for next execution

   //slot->tts_nvalid = attnum;
   StoreIndirect("TupleTableSlot", "tts_nvalid",
      Load("slot"),
	  ConvertTo(Int16,
	     Load("attnum")));

   //*offp = off;
   StoreAt(
	  Load("offp"),
	  Load("off"));

   //if (slow)
   OMR::JitBuilder::IlBuilder *slow_final_match = NULL;
   OMR::JitBuilder::IlBuilder *slow_final_match_else = NULL;

   IfThenElse(&slow_final_match, &slow_final_match_else,
      GreaterThan(
         Load("slow"),
		 ConstInt32(0)));

   //slot->tts_flags |= TTS_FLAG_SLOW; TTS_FLAG_SLOW= (1 <<3) = 8
   slow_final_match->StoreIndirect("TupleTableSlot", "tts_flags",
   slow_final_match->   Load("slot"),
   slow_final_match->   Or(
   slow_final_match->      LoadIndirect("TupleTableSlot", "tts_flags",
   slow_final_match->         Load("slot")),
   slow_final_match->      ConstInt16(TTS_FLAG_SLOW)));

   //slot->tts_flags &= ~TTS_FLAG_SLOW; TTS_FLAG_SLOW= (1 <<3) = 8
   slow_final_match_else->StoreIndirect("TupleTableSlot", "tts_flags",
   slow_final_match_else->   Load("slot"),
   slow_final_match_else->   And(
   slow_final_match_else->      LoadIndirect("TupleTableSlot", "tts_flags",
   slow_final_match_else->         Load("slot")),
   slow_final_match_else->      ConstInt16(~TTS_FLAG_SLOW)));

   Return();
   return true;


   }



extern "C" {
PG_MODULE_MAGIC;

/*function to compile tuple deformation Jit code*/
void omr_compile(){
	//elog(INFO, "Step 2: define type dictionaries\n");
	StructTypeDictionary joinmethodTypes;
	//elog(INFO, "Step 3: compile slot_deform method builder\n");
	slot_compile_deform method(&joinmethodTypes);
	void *entry=0;
	int32_t rc = compileMethodBuilder(&method, &entry);

	if (rc != 0)
	{
	   //fprintf(stderr,"FAIL: compilation error %d\n", rc);
		elog(INFO, "FAIL: compilation error %d\n", rc);
	   exit(-2);
	}
	slot_deform = (OMRJIT_slot_deformFunctionType *)entry;

}


/*This function was used earlier for doing the compilation and invoking.
 * We don't need it now and can be used for testing purposes*/
void omr_tuple_deform(int32_t natts, TupleTableSlot *slot, HeapTuple tuple, uint32 *offp)
{
	//printf("Step 1: initialize JIT\n");
	/*elog(INFO, "Step 1: initialize JIT\n");
	bool initialized = initializeJit();
	if (!initialized)
	{
	   //fprintf(stderr, "FAIL: could not initialize JIT\n");
	   elog(INFO, "FAIL: could not initialize JIT\n");
	   exit(-1);
	}*/

	//printf("Step 2: define type dictionaries\n");
	//elog(INFO, "Step 2: define type dictionaries\n");
	//StructTypeDictionary joinmethodTypes;

	//printf("Step 3: compile slot_deform method builder\n");
	//elog(INFO, "Step 3: compile slot_deform method builder\n");

	/*******************compile slot_deform*********************/

	/*slot_compile_deform method(&joinmethodTypes);
	void *entry=0;
	int32_t rc = compileMethodBuilder(&method, &entry);

	if (rc != 0)
	{
	   //fprintf(stderr,"FAIL: compilation error %d\n", rc);
		elog(INFO, "FAIL: compilation error %d\n", rc);
	   exit(-2);
	}*/

	/*******************invoke slot_deform**************************************/
	//printf("Step 4: invoke slot_deform compiled code\n");
	/*elog(INFO, "Step 4: invoke slot_deform compiled code\n");

	OMRJIT_slot_deformFunctionType *deform = (OMRJIT_slot_deformFunctionType *)entry;*/
	//deform(natts, slot, tuple, offp);
	slot_deform(natts, slot, tuple, offp);
	//cout << "Step 5: shutdown JIT\n";
	//elog(INFO, "Step 5: shutdown JIT\n");
	//shutdownJit();
}

}


















