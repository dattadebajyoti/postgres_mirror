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
#include "jit/omr_operator.h"
#include "utils/expandeddatum.h"

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


static Datum
MakeExpandedObjectReadOnlyInternal_func(Datum d)
{
#define MakeExpandedObjectReadOnlyInternal_func_LINE LINETOSTR(__LINE__)

	ExpandedObjectHeader *eohptr;

	/* Nothing to do if not a read-write expanded-object pointer */
	if (!VARATT_IS_EXTERNAL_EXPANDED_RW(DatumGetPointer(d)))
		return d;

	/* Now safe to extract the object pointer */
	eohptr = DatumGetEOHP(d);

	/* Return the built-in read-only pointer instead of given pointer */
	return EOHPGetRODatum(eohptr);
}

//VARSIZE_ANY_func
static size_t VARSIZE_ANY_func(void* attptr) {
    #define VARSIZE_ANY_func_LINE LINETOSTR(__LINE__)

	return ((int32_t)VARSIZE_ANY(attptr));
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
static void print_func(int32_t m) {
    #define PRINTFUNC_LINE LINETOSTR(__LINE__)

	elog(INFO, "natts in print: %d\n", m);

}


static char* tp_func(HeapTupleHeader tup) {
    #define TPFUNC_LINE LINETOSTR(__LINE__)

	return ((char *) tup + tup->t_hoff);

}

/* return att_align_nominal */
static int32_t att_addlength_pointer_func(int32_t off, int16_t attlen, char * attptr) {
    #define ATTADDLENFUNC_LINE LINETOSTR(__LINE__)
	return att_addlength_pointer(off, attlen, attptr);

}

/* return fetchatt */
static Datum fetchatt_func(Form_pg_attribute A, char * T, int32_t off) {
    #define FETCHATTFUNC_LINE LINETOSTR(__LINE__)

	return fetchatt(A, T);

}

/* return att_align_nominal */
static int32_t att_align_nominal_func(int32_t cur_offset, char attalign) {
    #define ATTALIGNNOMINALFUNC_LINE LINETOSTR(__LINE__)
	return att_align_nominal(cur_offset, attalign);

}


/* return att_align_pointer */
static int32_t att_align_pointer_func(int32_t cur_offset, char attalign, int32_t attlen, char * attptr) {
    #define ATTALIGNPTRFUNC_LINE LINETOSTR(__LINE__)

	return att_align_pointer(cur_offset, attalign, attlen, attptr + cur_offset);

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
   OMR::JitBuilder::IlType *TupleTableSlotDesc;
   OMR::JitBuilder::IlType *pTupleTableSlot;
   OMR::JitBuilder::IlType *psize_t;



   public:

      slot_compile_deform(OMR::JitBuilder::TypeDictionary *);

      OMR::JitBuilder::IlValue* fetch_attributes(IlBuilder *, OMR::JitBuilder::IlValue *, OMR::JitBuilder::IlValue *, OMR::JitBuilder::IlValue *);
      OMR::JitBuilder::IlValue* att_align_nominal_cal(IlBuilder *, OMR::JitBuilder::IlValue *, OMR::JitBuilder::IlValue *);
      OMR::JitBuilder::IlValue* att_addlength_pointer_cal(IlBuilder *, OMR::JitBuilder::IlValue *, OMR::JitBuilder::IlValue *, OMR::JitBuilder::IlValue *);
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
   psize_t = types->toIlType<size_t>();

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

   TupleTableSlotDesc = types->LookupStruct("TupleTableSlot");
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
				  psize_t,
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

   DefineFunction((char *)"store_isnull",
                  (char *)__FILE__,
                  (char *)ISNULL_LINE,
                  (void *)&store_isnull,
				  NoType,
                  2,
				  Int32, Int16);

   /* Define Return type */
   DefineReturnType(NoType);

   }

class StructTypeDictionary : public OMR::JitBuilder::TypeDictionary
   {
   public:

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
	   	   /*OMR::JitBuilder::IlType *HeapTupleDataType =*/ DefineStruct("HeapTupleData");

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

	   	   /*OMR::JitBuilder::IlType *FormData_pg_attributeType =*/ DEFINE_STRUCT(FormData_pg_attribute);
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
	   	   /*OMR::JitBuilder::IlType *AttrDefaultType =*/ DefineStruct("AttrDefault");
	   	   //OMR::JitBuilder::IlType *pAttrDefaultType = PointerTo("AttrDefault");

	   	   DefineField("AttrDefault", "adnum", Int16);
	   	   DefineField("AttrDefault", "adbin", d.toIlType<char *>());

	   	   CLOSE_STRUCT(AttrDefault);

	   	   /*********Declare ConstrCheck***********/
	   	   /*OMR::JitBuilder::IlType *ConstrCheckType =*/ DefineStruct("ConstrCheck");
	   	   //OMR::JitBuilder::IlType *pConstrCheckType = PointerTo("ConstrCheck");

	   	   DefineField("ConstrCheck", "ccname", d.toIlType<char *>());
	   	   DefineField("ConstrCheck", "ccbin", d.toIlType<char *>());
	   	   DefineField("ConstrCheck", "ccvalid", Int32);
	   	   DefineField("ConstrCheck", "ccnoinherit", Int32);

	   	   CloseStruct("ConstrCheck");

	   	   /*********Declare AttrMissing***********/
	   	   /*OMR::JitBuilder::IlType *AttrMissingType =*/ DefineStruct("AttrMissing");
	   	   //OMR::JitBuilder::IlType *pAttrMissingType = PointerTo("AttrMissing");

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

	   	   /*OMR::JitBuilder::IlType *TupleDescType =*/ DEFINE_STRUCT(TupleDescData);
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
	   	   /*OMR::JitBuilder::IlType *TupleTableSlotType =*/ DEFINE_STRUCT(TupleTableSlot);

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
	attlen_match1->      ConvertTo(Int32, cur_offset)));

	OMR::JitBuilder::IlBuilder *attlen_match2 = NULL;
	OMR::JitBuilder::IlBuilder *attlen_match2_else = NULL;

	attlen_match1_else->IfThenElse(&attlen_match2, &attlen_match2_else,
	attlen_match1_else->   EqualTo(
	attlen_match1_else->      ConvertTo(Int32, attlen),
	attlen_match1_else->      ConstInt32(-1)));

	//(cur_offset) + VARSIZE_ANY(attptr)
	attlen_match2->Store("offset",
	attlen_match2->ConvertTo(Int32,
    attlen_match2->   Add(
	attlen_match2->      ConvertTo(Int32, cur_offset),
	attlen_match2->      ConvertTo(Int32,
    attlen_match2->         Call("VARSIZE_ANY_func", 1,
	attlen_match2->            ConvertTo(pStr, attptr))))));

	//(cur_offset) + (strlen((char *) (attptr)) + 1)
	attlen_match2_else->Store("offset",
	attlen_match2_else->   ConvertTo(Int32,
	attlen_match2_else->      Add(
	attlen_match2_else->         ConvertTo(Int32, cur_offset),
	attlen_match2_else->         Add(
	attlen_match2_else->            ConstInt32(1),
	attlen_match2_else->            ConvertTo(Int32,
	attlen_match2_else->               Call("strlen_func",1,
    attlen_match2_else->                  ConvertTo(pStr, attptr))))))     );

	return b->ConvertTo(Int32, b->Load("offset"));

}

OMR::JitBuilder::IlValue*
slot_compile_deform::att_align_nominal_cal(IlBuilder *b, OMR::JitBuilder::IlValue *cur_offset, OMR::JitBuilder::IlValue *attalign)
{

	//OMR::JitBuilder::IlValue *off = b->ConstInt32(0);
	b->Store("cal_off",
	b->   ConstInt32(0));

	OMR::JitBuilder::IlBuilder *TYPALIGN_INT_match = NULL;
	OMR::JitBuilder::IlBuilder *TYPALIGN_INT_match_else = NULL;

	//if
	b->IfThenElse(&TYPALIGN_INT_match, &TYPALIGN_INT_match_else,
    b->   EqualTo(
	b->      ConvertTo(Int32, attalign),
	b->      ConstInt32(TYPALIGN_INT)));

	//#define INTALIGN(LEN)	  TYPEALIGN(ALIGNOF_INT, (LEN))
	//#define TYPEALIGN(ALIGNVAL,LEN)
	//   (((uintptr_t) (LEN) + ((ALIGNVAL) - 1)) & ~((uintptr_t) ((ALIGNVAL) - 1))) = (((uintptr_t) (LEN) + 3) & ~((uintptr_t) 3))
	TYPALIGN_INT_match->Store("cal_off",
	TYPALIGN_INT_match->   ConvertTo(Int32,
    TYPALIGN_INT_match->   And(
    TYPALIGN_INT_match->      Add(
    TYPALIGN_INT_match->	     ConvertTo(Int32, cur_offset),
	TYPALIGN_INT_match->         ConstInt32(3)),
    TYPALIGN_INT_match->      ConstInt32(~3)))    );
	//TYPALIGN_INT_match->Call("print_func", 2, cur_offset, TYPALIGN_INT_match->ConvertTo(Int32, TYPALIGN_INT_match->Load("cal_off")));

    //else
	OMR::JitBuilder::IlBuilder *TYPALIGN_CHAR_match = NULL;
	OMR::JitBuilder::IlBuilder *TYPALIGN_CHAR_match_else = NULL;

	//if
	//(((attalign) == TYPALIGN_CHAR) ?
	TYPALIGN_INT_match_else->IfThenElse(&TYPALIGN_CHAR_match, &TYPALIGN_CHAR_match_else,
	TYPALIGN_INT_match_else->   EqualTo(
    TYPALIGN_INT_match_else->      ConvertTo(Int32,attalign),
    TYPALIGN_INT_match_else->      ConstInt32(TYPALIGN_CHAR)));

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
	TYPALIGN_CHAR_match_else->      ConvertTo(Int32,attalign),
    TYPALIGN_CHAR_match_else->      ConstInt32(TYPALIGN_DOUBLE)));

	//#define DOUBLEALIGN(LEN)	  TYPEALIGN(ALIGNOF_DOUBLE, (LEN))
	//#define TYPEALIGN(ALIGNVAL,LEN)
	//   (((uintptr_t) (LEN) + ((ALIGNVAL) - 1)) & ~((uintptr_t) ((ALIGNVAL) - 1))) = (((uintptr_t) (LEN) + 7) & ~((uintptr_t) 7))
	TYPALIGN_DOUBLE_match->Store("cal_off",
    TYPALIGN_DOUBLE_match->   ConvertTo(Int32,
    TYPALIGN_DOUBLE_match->   And(
	TYPALIGN_DOUBLE_match->      Add(
    TYPALIGN_DOUBLE_match->         ConvertTo(Int32, cur_offset),
	TYPALIGN_DOUBLE_match->         ConstInt32(7)),
	TYPALIGN_DOUBLE_match->      ConstInt32(~7)))    );
	//TYPALIGN_DOUBLE_match->Call("print_func", 2, cur_offset, TYPALIGN_DOUBLE_match->ConvertTo(Int32, off));

	//else

	//#define SHORTALIGN(LEN)	TYPEALIGN(ALIGNOF_SHORT, (LEN))
	//#define TYPEALIGN(ALIGNVAL,LEN)
	//   (((uintptr_t) (LEN) + ((ALIGNVAL) - 1)) & ~((uintptr_t) ((ALIGNVAL) - 1))) = (((uintptr_t) (LEN) + 1) & ~((uintptr_t) 1))
	TYPALIGN_DOUBLE_match_else->Store("cal_off",
	TYPALIGN_DOUBLE_match_else->   ConvertTo(Int32,
	TYPALIGN_DOUBLE_match_else->   And(
	TYPALIGN_DOUBLE_match_else->      Add(
    TYPALIGN_DOUBLE_match_else->         ConvertTo(Int32, cur_offset),
	TYPALIGN_DOUBLE_match_else->         ConstInt32(1)),
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
	off_align_ptr_flag_match->   ConvertTo(Int32, att_align_nominal_cal(off_align_ptr_flag_match, cur_offset, attalign)   ));


    return b->Load("off_align_ptr");


}

OMR::JitBuilder::IlValue*
slot_compile_deform::fetch_attributes(IlBuilder *b, OMR::JitBuilder::IlValue *thisatt, OMR::JitBuilder::IlValue *tp, OMR::JitBuilder::IlValue *offset)
{

	b->Store("att", b->ConvertTo(Address,b->ConstInt32(0)));

	b->Store("attlen",
	b->   ConvertTo(Int32,
	b->      LoadIndirect("FormData_pg_attribute", "attlen",thisatt)));

	b->Store("attbyval",
	b->   ConvertTo(bool_type, b->LoadIndirect("FormData_pg_attribute", "attbyval", thisatt)));

    // For byval: datums copy the value, extend to Datum's width, and store.
    OMR::JitBuilder::IlBuilder *attbyval_match = NULL;
    OMR::JitBuilder::IlBuilder *attbyval_match_else = NULL;

    //If byval true
    b->IfThenElse(&attbyval_match, &attbyval_match_else,
    b->   EqualTo(
    b->	  ConvertTo(bool_type, b->Load("attbyval")),
	b->	  ConvertTo(bool_type, b->ConstInt16(1))));

    //------------------By Value--------------------------

    //Translation for:  (attlen) == (int) sizeof(Datum) ?
    OMR::JitBuilder::IlBuilder *attlenDat_match = NULL;
    OMR::JitBuilder::IlBuilder *attlenDat_match_else = NULL;

    //if of datum
    attbyval_match->IfThenElse(&attlenDat_match, &attlenDat_match_else,
    attbyval_match->   EqualTo(
    attbyval_match->      Load("attlen"),
    attbyval_match->      ConstInt32((int) sizeof(Datum))));

    //Translation for:  *((Datum *)(T))
    //attlenDat_match->Store("att", /*attlenDat_match->ConvertTo(datum_rep, */attlenDat_match->ConvertTo(pDatum, attlenDat_match->ConvertTo(pStr, tp)));
    attlenDat_match->Store("att", attlenDat_match->ConvertTo(Address,attlenDat_match->Call("t_datum_func",1, attlenDat_match->ConvertTo(pStr, tp))));

    //else of datum
    //Check for Int32 representation i.e (attlen) == (int) sizeof(int32) ?
    OMR::JitBuilder::IlBuilder *attlenInt32_match = NULL;
    OMR::JitBuilder::IlBuilder *attlenInt32_match_else = NULL;

    //if int32
    attlenDat_match_else->IfThenElse(&attlenInt32_match, &attlenInt32_match_else,
    attlenDat_match_else->   EqualTo(
    attlenDat_match_else->      Load("attlen"),
    attlenDat_match_else->      ConstInt32((int) sizeof(int32))));

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
	attlenInt32_match_else->      ConstInt32((int) sizeof(int16))));

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


/******************************BUILDIL Tuple deformation**********************************************/

bool
slot_compile_deform::buildIL()
   {

   /*************************Convert the interpreted model**************************************/

	//TupleDesc	tupleDesc = slot_opt->tts_tupleDescriptor;
	Store("tupleDesc",
	   LoadIndirect("TupleTableSlot","tts_tupleDescriptor",
	      Load("slot")));

	//HeapTupleHeader tup = tuple_opt->t_data;
    Store("tup",
	   LoadIndirect("HeapTupleData", "t_data",
		  Load("tuple")));

    Store("tp1",
	   Call("tp_func", 1, Load("tup")));

	//uint32		off;			/* offset in tuple data */
	Store("off", ConstInt32(0));

	//bool		slow;			/* can we use/set attcacheoff? */
	Store("slow", ConvertTo(bool_type, ConstInt16(false)));

	/* We can only fetch as many attributes as the tuple has. */

	Store("HeapTupleHeaderGetNatts",
	   And(
	      ConvertTo(Int32, LoadIndirect("HeapTupleHeaderData", "t_infomask2",
	         Load("tup"))),
		  ConstInt32(HEAP_NATTS_MASK)));//HEAP_NATTS_MASK = 2047

	//find the min
	OMR::JitBuilder::IlBuilder *natts_min_match = NULL;
	IfThen(&natts_min_match,
	   LessThan(
	      Load("HeapTupleHeaderGetNatts"),
	      ConvertTo(Int32,
	         Load("natts"))));
	{
		natts_min_match->Store("natts",
	    natts_min_match->   Load("HeapTupleHeaderGetNatts"));
	}

	//bool hasnulls = HeapTupleHasNulls(tuple);  (((tuple)->t_data->t_infomask & 0x0001) != 0)
    Store("hasnulls", ConstInt32(0));

	OMR::JitBuilder::IlBuilder *nulls_check = NULL;
	IfThen(&nulls_check,
	   NotEqualTo(
	      And(
	         ConstInt16(1),
	         ConvertTo(Int16,
	            LoadIndirect("HeapTupleHeaderData", "t_infomask2",
	        	   LoadIndirect("HeapTupleData", "t_data",
	        	      Load("tuple")) )  )),
		  ConstInt16(0)));
	{
		nulls_check->Store("hasnulls",
	    nulls_check->   ConstInt32(1));
	}


	/*
	 * Check whether the first call for this tuple, and initialize or restore
	 * loop state.
	 */
	//attnum = slot_opt->tts_nvalid;
	Store("attnum",
	   ConvertTo(Int32, LoadIndirect("TupleTableSlot", "tts_nvalid",
	      Load("slot"))));

	OMR::JitBuilder::IlBuilder *attnum_match = NULL;
	IfThen(&attnum_match,
	   NotEqualTo(
	      Load("attnum"),
	      ConstInt32(0)));

	//if(attnum != 0)
	{
		//Restore state from previous execution
		//off = *off_opt;
		attnum_match->Store("off",
	    attnum_match->   ConvertTo(Int32,
	    attnum_match->      LoadAt(pInt32,
	    attnum_match->         Load("offp"))));

		//slow = TTS_SLOW(slot_opt);
		attnum_match->Store("slow",
		attnum_match->   ConvertTo(bool_type,
		attnum_match->      NotEqualTo(
		attnum_match->         And(
		attnum_match->            LoadIndirect("TupleTableSlot", "tts_flags",
		attnum_match->               Load("slot")),
		attnum_match->            ConstInt16(8)),
		attnum_match->		   ConstInt16(0))));
	}


	OMR::JitBuilder::IlBuilder *loop = NULL;
	ForLoopUp("attnum_index", &loop,
	   ConvertTo(Int32, Load("attnum")),
	   ConvertTo(Int32, Load("natts")),
	   ConstInt32(1));

	{
		//Form_pg_attribute thisatt = TupleDescAttr(tupleDesc, attnum);
		loop->Store("thisatt",
		loop->   IndexAt(pFormData_pg_attribute,
		loop->      StructFieldInstanceAddress("TupleDescData", "attrs",
		loop->         Load("tupleDesc")),
		loop->       ConvertTo(Int32,
		loop->          Load("attnum")))            );

		//if hasnull
		IlBuilder *hasnull_builder = loop->OrphanBuilder();
		OMR::JitBuilder::IlValue *hasnull_L = hasnull_builder->EqualTo(
											  hasnull_builder->   Load("hasnulls"),
											  hasnull_builder->   ConstInt32(1));

        //if att_isnull :- att_isnull(ATT, BITS) (!((BITS)[(ATT) >> 3] & (1 << ((ATT) & 0x07))))
		IlBuilder *att_isnull_builder = loop->OrphanBuilder();
		OMR::JitBuilder::IlValue *att_isnull_R = att_isnull_builder->NotEqualTo(
												 att_isnull_builder->      And(
												 att_isnull_builder->         ConvertTo(Int32,
												 att_isnull_builder->            LoadAt(pBits8,
												 att_isnull_builder->               IndexAt(pBits8,
												 att_isnull_builder->                  LoadIndirect("HeapTupleHeaderData", "t_bits",
												 att_isnull_builder->                     Load("tup")),
												 att_isnull_builder->                  ShiftR(
												 att_isnull_builder->                     ConvertTo(Int32,
												 att_isnull_builder->                        Load("attnum")),
												 att_isnull_builder->                     ConstInt32(3))))),
												 att_isnull_builder->         ShiftL(
												 att_isnull_builder->            ConstInt32(1),
												 att_isnull_builder->            And(
												 att_isnull_builder->               ConvertTo(Int32,
												 att_isnull_builder->				   Load("attnum")),
												 att_isnull_builder->               ConstInt32(7)))),
												 att_isnull_builder->      ConstInt32(0));


		IlBuilder *null_true = NULL, *null_false = NULL;
		loop->IfAnd(&null_true, &null_false, 2,
		loop->   MakeCondition(hasnull_builder, hasnull_L),
		loop->   MakeCondition(att_isnull_builder, att_isnull_R));

		//values[attnum] = (Datum) 0;
		null_true->StoreAt(
		null_true->   IndexAt(pDatum,
		null_true->      LoadIndirect("TupleTableSlot", "tts_values",
		null_true->         Load("slot")),
		null_true->	  ConvertTo(Int32,
		null_true->	     Load("attnum"))),
		null_true->   ConvertTo(Address,
	    null_true->	     ConstInt32(0)));

		//isnull[attnum] = true;
		null_true->StoreAt(
		null_true->   IndexAt(pbool,
		null_true->      LoadIndirect("TupleTableSlot", "tts_isnull",
		null_true->         Load("slot")),
		null_true->      ConvertTo(Int32,
		null_true->         Load("attnum"))),
		null_true->   ConvertTo(bool_type,
		null_true->      ConstInt16(true)));

		//slow = true;
		null_true->Store("slow",
		null_true->   ConvertTo(bool_type,
		null_true->      ConstInt16(true)));


        //continue

		//isnull[attnum] = false;
		null_false->StoreAt(
		null_false->   IndexAt(pbool,
		null_false->      LoadIndirect("TupleTableSlot", "tts_isnull",
		null_false->         Load("slot")),
		null_false->		 ConvertTo(Int32,
		null_false->          Load("attnum"))),
		null_false->   ConvertTo(bool_type,
		null_false->      ConstInt16(false)));

		IlBuilder *x_ge_L_builder = null_false->OrphanBuilder();
		OMR::JitBuilder::IlValue *x_ge_L = x_ge_L_builder->NotEqualTo(
		                                      x_ge_L_builder->   ConvertTo(bool_type,
		                                      x_ge_L_builder->      Load("slow")),
		                                      x_ge_L_builder->   ConvertTo(bool_type,
		                                      x_ge_L_builder->      ConstInt16(true)));

		IlBuilder *x_lt_U_builder = null_false->OrphanBuilder();
		OMR::JitBuilder::IlValue *x_lt_U = x_lt_U_builder->GreaterOrEqualTo(
		                                      x_lt_U_builder->   ConvertTo(Int32,
		                                      x_lt_U_builder->      LoadIndirect("FormData_pg_attribute", "attcacheoff",
		                                      x_lt_U_builder->         Load("thisatt"))),
		                                      x_lt_U_builder->   ConstInt32(0));


		IlBuilder *rc1True = NULL, *rc1false = NULL;
		null_false->IfAnd(&rc1True, &rc1false, 2,
		null_false->   MakeCondition(x_ge_L_builder, x_ge_L),
		null_false->   MakeCondition(x_lt_U_builder, x_lt_U));

	    //in-if ... off = thisatt->attcacheoff;
		rc1True->Store("off",
		rc1True->   ConvertTo(Int32,
		rc1True->      LoadIndirect("FormData_pg_attribute", "attcacheoff",
		rc1True->         Load("thisatt"))));


		OMR::JitBuilder::IlBuilder *thisatt_attlen_negative_match = NULL;
		OMR::JitBuilder::IlBuilder *thisatt_attlen_negative_match_else = NULL;

		//in-else if ... if(thisatt->attlen == -1)
		rc1false->IfThenElse(&thisatt_attlen_negative_match, &thisatt_attlen_negative_match_else,
		rc1false->   EqualTo(
		rc1false->      ConvertTo(Int16,
		rc1false->         LoadIndirect("FormData_pg_attribute", "attlen",//suspicious
		rc1false->            Load("thisatt"))),
		rc1false->      ConstInt16(-1)));

		//in-else if ...  if(!slow)
		IlBuilder *x_ge_L_builder1 = thisatt_attlen_negative_match->OrphanBuilder();
		OMR::JitBuilder::IlValue *x_ge_L1 = x_ge_L_builder1->NotEqualTo(
		                                      x_ge_L_builder1->   ConvertTo(bool_type,
		                                      x_ge_L_builder1->      Load("slow")),
		                                      x_ge_L_builder1->   ConvertTo(bool_type,
		                                      x_ge_L_builder1->      ConstInt16(true)));

		//in-else if ... off == att_align_nominal(off, thisatt->attalign)
		IlBuilder *x_lt_U_builder1 = thisatt_attlen_negative_match->OrphanBuilder();
		OMR::JitBuilder::IlValue *x_lt_U1 = x_lt_U_builder1->EqualTo(
		                                      x_lt_U_builder1->   Load("off"),
		                                      x_lt_U_builder1->   ConvertTo(Int32, att_align_nominal_cal(x_lt_U_builder1,
		                                      x_lt_U_builder1->      ConvertTo(Int32,
		                                      x_lt_U_builder1->         Load("off")),
											  x_lt_U_builder1->      LoadIndirect("FormData_pg_attribute", "attalign",
											  x_lt_U_builder1->         Load("thisatt"))))      );

		IlBuilder *rc1True1 = NULL, *slow_off_att_align_nominal_match_else = NULL;
		thisatt_attlen_negative_match->IfAnd(&rc1True1, &slow_off_att_align_nominal_match_else, 2,
		thisatt_attlen_negative_match->   MakeCondition(x_ge_L_builder1, x_ge_L1),
		thisatt_attlen_negative_match->   MakeCondition(x_lt_U_builder1, x_lt_U1));

		rc1True1->StoreIndirect("FormData_pg_attribute", "attcacheoff",
		rc1True1->   Load("thisatt"),
		rc1True1->   ConvertTo(Int32,
		rc1True1->      Load("off")));

		//in-else if ... off = att_align_pointer_cal
		slow_off_att_align_nominal_match_else->Store("off",
	    slow_off_att_align_nominal_match_else->   ConvertTo(Int32,
		att_align_pointer_cal(                        slow_off_att_align_nominal_match_else,
	    slow_off_att_align_nominal_match_else->          Load("off"),
		slow_off_att_align_nominal_match_else->          LoadIndirect("FormData_pg_attribute", "attalign",
		slow_off_att_align_nominal_match_else->             Load("thisatt")),
		slow_off_att_align_nominal_match_else->          ConstInt32(-1),
		slow_off_att_align_nominal_match_else->          Add(
		slow_off_att_align_nominal_match_else->             Load("tp1"),
		slow_off_att_align_nominal_match_else->             Load("off"))   )));

		//in-else if ... slow = true;
		slow_off_att_align_nominal_match_else->Store("slow",
	    slow_off_att_align_nominal_match_else->   ConvertTo(bool_type,
		slow_off_att_align_nominal_match_else->      ConstInt16(true)));

        //in-else
		thisatt_attlen_negative_match_else->Store("off",
		thisatt_attlen_negative_match_else->   ConvertTo(Int32,
				                               att_align_nominal_cal(thisatt_attlen_negative_match_else,
	    thisatt_attlen_negative_match_else->      ConvertTo(Int32,
	    thisatt_attlen_negative_match_else->         Load("off")),
		thisatt_attlen_negative_match_else->      LoadIndirect("FormData_pg_attribute", "attalign",
		thisatt_attlen_negative_match_else->         Load("thisatt")))));

		//in-else ... if (!slow)
		OMR::JitBuilder::IlBuilder *slow_thisatt_attlen_negative_match_else = NULL;

		thisatt_attlen_negative_match_else->IfThen(&slow_thisatt_attlen_negative_match_else,
		thisatt_attlen_negative_match_else->   NotEqualTo(
		thisatt_attlen_negative_match_else->      ConvertTo(bool_type,
		thisatt_attlen_negative_match_else->         Load("slow")),
		thisatt_attlen_negative_match_else->      ConvertTo(bool_type,
		thisatt_attlen_negative_match_else->         ConstInt16(true))));

		//in-else ... thisatt->attcacheoff = off;
		slow_thisatt_attlen_negative_match_else->StoreIndirect("FormData_pg_attribute", "attcacheoff",
		slow_thisatt_attlen_negative_match_else->   Load("thisatt"),
		slow_thisatt_attlen_negative_match_else->   ConvertTo(Int32,
		slow_thisatt_attlen_negative_match_else->      Load("off")));

		//values[attnum] = fetchatt(thisatt, tp + off);
		null_false->StoreAt(
		null_false->   IndexAt(pDatum,
		null_false->      LoadIndirect("TupleTableSlot", "tts_values",
		null_false->         Load("slot")),
		null_false->		 ConvertTo(Int32,
		null_false->          Load("attnum"))),
		null_false->   ConvertTo(Address,
			  fetch_attributes(null_false,
		null_false->         Load("thisatt"),
		null_false->         Add(
		null_false->            Load("tp1"),
		null_false->			  ConvertTo(Int32,
		null_false->			     Load("off"))),
		null_false->		   ConvertTo(Int32,
		null_false->            Load("off")))));

		//off = att_addlength_pointer(off, thisatt->attlen, tp + off);
		null_false->Store("off",
		null_false->   ConvertTo(Int32,
		     att_addlength_pointer_cal(null_false,
		null_false->         ConvertTo(Int32,
		null_false->		      Load("off")),
		null_false->         LoadIndirect("FormData_pg_attribute", "attlen",
		null_false->            Load("thisatt")),
		null_false->         Add(
		null_false->            Load("tp1"),
		null_false->			  ConvertTo(Int32,
		null_false->               Load("off")))          )));

		/* can't use attcacheoff anymore */

		OMR::JitBuilder::IlBuilder *thisatt_attlen_match = NULL;
		null_false->IfThen(&thisatt_attlen_match,
		null_false->   LessOrEqualTo(
		null_false->      ConvertTo(Int32,
		null_false->         LoadIndirect("FormData_pg_attribute", "attlen",
		null_false->            Load("thisatt"))),
		null_false->      ConstInt32(0)));

		{
		//slow = true;
		thisatt_attlen_match->Store("slow",
		thisatt_attlen_match->   ConvertTo(bool_type,
		thisatt_attlen_match->      ConstInt16(true)));

		}

		loop->Store("attnum",
		loop->   Add(
		loop->      Load("attnum"),
		loop->      ConstInt32(1)));
	}

	/*
	 * Save state for next execution
	 */
	//slot_opt->tts_nvalid = attnum;
	StoreIndirect("TupleTableSlot", "tts_nvalid",
	   Load("slot"),
	   ConvertTo(Int16, Load("attnum")));

	//*off_opt = off;
	StoreAt(
	   Load("offp"),
	   ConvertTo(Int32, Load("off")));


	OMR::JitBuilder::IlBuilder *slow_final_match = NULL;
	OMR::JitBuilder::IlBuilder *slow_final_match_else = NULL;

	IfThenElse(&slow_final_match, &slow_final_match_else,
	   EqualTo(
	      ConvertTo(bool_type, Load("slow")),
	      ConvertTo(bool_type, ConstInt16(true))));
	{
    //if (slow)
	//slot->tts_flags |= TTS_FLAG_SLOW; TTS_FLAG_SLOW= (1 <<3) = 8
	slow_final_match->StoreIndirect("TupleTableSlot", "tts_flags",
	slow_final_match->   Load("slot"),
	slow_final_match->   Or(
	slow_final_match->      ConvertTo(Int16, slow_final_match->LoadIndirect("TupleTableSlot", "tts_flags",
	slow_final_match->         Load("slot"))),
	slow_final_match->      ConstInt16(TTS_FLAG_SLOW)));

	}

	{
	//else
	//slot->tts_flags &= ~TTS_FLAG_SLOW; TTS_FLAG_SLOW= (1 <<3) = 8
	slow_final_match_else->StoreIndirect("TupleTableSlot", "tts_flags",
	slow_final_match_else->   Load("slot"),
	slow_final_match_else->   And(
	slow_final_match_else->      ConvertTo(Int16, slow_final_match_else->LoadIndirect("TupleTableSlot", "tts_flags",
	slow_final_match_else->         Load("slot"))),
	slow_final_match_else->      ConstInt16(~TTS_FLAG_SLOW)));

	}


   Return();
   return true;


   }


/*End*/

class EEOP_QUAL_class : public OMR::JitBuilder::MethodBuilder
{
protected:
	OMR::JitBuilder::IlType *pB;
	OMR::JitBuilder::IlType *pBool;
	OMR::JitBuilder::IlType *pD;
	OMR::JitBuilder::IlType *pDatum;
public:
	EEOP_QUAL_class(OMR::JitBuilder::TypeDictionary *);
	virtual bool buildIL();
};

EEOP_QUAL_class::EEOP_QUAL_class(OMR::JitBuilder::TypeDictionary *types)
   : OMR::JitBuilder::MethodBuilder(types)
   {
   DefineLine(LINETOSTR(__LINE__));
   DefineFile(__FILE__);

   DefineName("EEOP_QUAL");

   pBool = types->toIlType<bool **>();
   pB = types->toIlType<bool *>();

   pDatum = types->toIlType<Datum **>();
   pD = types->toIlType<Datum *>();

   DefineParameter("resnull",    pBool);
   DefineParameter("resvalue",     pDatum);

   DefineReturnType(Int32);
   }

bool
EEOP_QUAL_class::buildIL()
{
	Store("check_false", ConstInt32(0));

	//IfOr
	   IlBuilder *x_ge_L_builder2 = OrphanBuilder();
	   OMR::JitBuilder::IlValue *x_ge_L2 = x_ge_L_builder2->EqualTo(
			   	   	   	   	   	   	   	   x_ge_L_builder2->   ConvertTo(Int32,
			   	   	   	   	   	       	   x_ge_L_builder2->      LoadAt(pB, x_ge_L_builder2->Load("resnull"))),
				                           x_ge_L_builder2->   ConstInt32(1));

	   IlBuilder *x_lt_U_builder2 = OrphanBuilder();
	   OMR::JitBuilder::IlValue *x_lt_U2 = x_lt_U_builder2->EqualTo(
	                                      x_lt_U_builder2->   ConvertTo(Int32,
	                                      x_lt_U_builder2->      LoadAt(pD, x_lt_U_builder2->Load("resvalue"))),
	                                      x_lt_U_builder2->   ConstInt32(0));

	   IlBuilder *rcTrue = NULL, *rcFalse = NULL;
	   IfOr(&rcTrue, &rcFalse, 2,
	   MakeCondition(x_ge_L_builder2, x_ge_L2),
	   MakeCondition(x_lt_U_builder2, x_lt_U2));

	   //*op->resnull = false;
	   rcTrue->StoreAt(rcTrue->LoadAt(pBool, rcTrue->Load("resnull")), rcTrue->ConstInt32(0));
	   //*op->resvalue = BoolGetDatum(false);
	   rcTrue->StoreAt(rcTrue->LoadAt(pDatum, rcTrue->Load("resvalue")), rcTrue->ConstInt32(0));

	   rcTrue->Store("check_false",
	   rcTrue->   ConstInt32(1));
	//

	Return(Load("check_false"));
	return true;
}

class EEOP_FUNCEXPR_STRICT_class : public OMR::JitBuilder::MethodBuilder
{
protected:
	OMR::JitBuilder::IlType *pNullableDatum;
	OMR::JitBuilder::IlType *FunctionCallInfoBaseDataStruct;
	OMR::JitBuilder::IlType *pInt32;
	OMR::JitBuilder::IlType *pBool;
	OMR::JitBuilder::IlType *pDatum;
	OMR::JitBuilder::IlType *pDat;
public:
	EEOP_FUNCEXPR_STRICT_class(OMR::JitBuilder::TypeDictionary *);
	virtual bool buildIL();
};

class StructTypeDictionary1 : public OMR::JitBuilder::TypeDictionary
   {
   public:

   StructTypeDictionary1() :
      OMR::JitBuilder::TypeDictionary()
      {
   	      DefineStruct("NullableDatum");
   	      //OMR::JitBuilder::IlType *pNullableDatumType = PointerTo(NullableDatumType);

   	      DefineField("NullableDatum", "value", toIlType<Datum >());
   	      DefineField("NullableDatum", "isnull", toIlType<bool>());

          CloseStruct("NullableDatum");

          //FunctionCallInfoBaseData
	   	  DEFINE_STRUCT(FunctionCallInfoBaseData);

	   	  DEFINE_FIELD(FunctionCallInfoBaseData, isnull, toIlType<bool>());

	   	  CLOSE_STRUCT(FunctionCallInfoBaseData);
      }
   };

EEOP_FUNCEXPR_STRICT_class::EEOP_FUNCEXPR_STRICT_class(OMR::JitBuilder::TypeDictionary *types)
   : OMR::JitBuilder::MethodBuilder(types)
   {
   DefineLine(LINETOSTR(__LINE__));
   DefineFile(__FILE__);

   DefineName("EEOP_FUNCEXPR_STRICT");

   pInt32 = types->PointerTo(Int32);

   pNullableDatum = types->PointerTo((char *)"NullableDatum");

   FunctionCallInfoBaseDataStruct = types->LookupStruct("FunctionCallInfoBaseData");

   pBool = types->toIlType<bool **>();

   pDatum = types->toIlType<Datum **>();
   pDat = types->toIlType<Datum>();

   DefineParameter("nargs",    Int32);
   DefineParameter("args",     pNullableDatum);
   DefineParameter("resnull",  pBool);
   DefineParameter("resvalue",  pDatum);
   DefineParameter("d",  pDat);
   DefineParameter("fcinfo",  FunctionCallInfoBaseDataStruct);

   DefineReturnType(Int32);
   }

bool
EEOP_FUNCEXPR_STRICT_class::buildIL()
   {
   Store("strictfail", ConstInt32(0));

   OMR::JitBuilder::IlBuilder* args_loop = NULL;
   ForLoopUp("argno", &args_loop,
      ConstInt32(0),
	  ConvertTo(Int32, Load("nargs")),
	  ConstInt32(1));

	OMR::JitBuilder::IlBuilder *isnull = NULL;
	OMR::JitBuilder::IlBuilder *isnullElse = NULL;
	args_loop->IfThenElse(&isnull, &isnullElse,
	args_loop->   EqualTo(
	args_loop->      ConvertTo(Int32,
	args_loop->         LoadIndirect("NullableDatum", "isnull",
	args_loop->            IndexAt(pNullableDatum,
	args_loop->               Load("args"),
	args_loop->               Load("argno"))    )),
	args_loop->      ConstInt32(1)));

	{
		isnull->Store("strictfail",
		isnull->   ConstInt32(1));
	}

	//else//
	{
		//fcinfo->isnull = false;
		isnullElse->StoreIndirect("FunctionCallInfoBaseData", "isnull", isnullElse->Load("fcinfo"), isnullElse->ConstInt8(false));
		//(*op->resvalue = d);
		isnullElse->StoreAt(isnullElse->LoadAt(pDatum, isnullElse->Load("resvalue")), isnullElse->Load("d"));
		//(*op->resnull = false);
		isnullElse->StoreAt(isnullElse->LoadAt(pBool, isnullElse->Load("resnull")), isnullElse->ConstInt8(false));
	}

	args_loop->Store("argno",
	args_loop->   ConvertTo(Int32,
	args_loop->      Load("nargs")));


	Return(Load("strictfail"));
	return true;

   }

/*
 *
 *
 *EEOP_NOT_DISTINCT
 *
 *
 * */
class EEOP_NOT_DISTINCT_class : public OMR::JitBuilder::MethodBuilder
{
protected:
	OMR::JitBuilder::IlType *pNullableDatum;
	OMR::JitBuilder::IlType *FunctionCallInfoBaseDataStruct;
	OMR::JitBuilder::IlType *pInt32;
	OMR::JitBuilder::IlType *pBool;
	OMR::JitBuilder::IlType *pDatum;
	OMR::JitBuilder::IlType *pDat;
public:
	EEOP_NOT_DISTINCT_class(OMR::JitBuilder::TypeDictionary *);
	virtual bool buildIL();
};

class StructTypeDictionary3 : public OMR::JitBuilder::TypeDictionary
   {
   public:

   StructTypeDictionary3() :
      OMR::JitBuilder::TypeDictionary()
      {
   	      DEFINE_STRUCT(NullableDatum);
   	      OMR::JitBuilder::IlType *pNullableDatumType = PointerTo("NullableDatum");

   	      DEFINE_FIELD(NullableDatum, value, toIlType<Datum >());
   	      DEFINE_FIELD(NullableDatum, isnull, toIlType<bool>());

          CLOSE_STRUCT(NullableDatum);

          //FunctionCallInfoBaseData
	   	  DEFINE_STRUCT(FunctionCallInfoBaseData);

	   	  DEFINE_FIELD(FunctionCallInfoBaseData, isnull, toIlType<bool>());
	   	  DEFINE_FIELD(FunctionCallInfoBaseData, args, pNullableDatumType);

	   	  CLOSE_STRUCT(FunctionCallInfoBaseData);
      }
   };

EEOP_NOT_DISTINCT_class::EEOP_NOT_DISTINCT_class(OMR::JitBuilder::TypeDictionary *types)
   : OMR::JitBuilder::MethodBuilder(types)
   {
   DefineLine(LINETOSTR(__LINE__));
   DefineFile(__FILE__);

   DefineName("EEOP_NOT_DISTINCT_method");

   pInt32 = types->PointerTo(Int32);

   pNullableDatum = types->PointerTo((char *)"NullableDatum");

   FunctionCallInfoBaseDataStruct = types->LookupStruct("FunctionCallInfoBaseData");

   pBool = types->toIlType<bool **>();

   pDatum = types->toIlType<Datum **>();
   pDat = types->toIlType<Datum>();

   DefineParameter("resnull",  pBool);
   DefineParameter("resvalue",  pDatum);
   DefineParameter("eqresult",  pDat);
   DefineParameter("fcinfo",  FunctionCallInfoBaseDataStruct);

   DefineReturnType(Int32);
   }

bool
EEOP_NOT_DISTINCT_class::buildIL()
   {

/*	FunctionCallInfo fcinfo = op->d.func.fcinfo_data;

	if (fcinfo->args[0].isnull && fcinfo->args[1].isnull)
	{
		*op->resvalue = BoolGetDatum(true);
		*op->resnull = false;
	}
	else if (fcinfo->args[0].isnull || fcinfo->args[1].isnull)
	{
		*op->resvalue = BoolGetDatum(false);
		*op->resnull = false;
	}
	else
	{
		Datum		eqresult;

		fcinfo->isnull = false;
		eqresult = op->d.func.fn_addr(fcinfo);
		*op->resvalue = eqresult;
		*op->resnull = fcinfo->isnull;
	}*/

	IlBuilder *args_0_isnull = OrphanBuilder();
	OMR::JitBuilder::IlValue *hasnull_L =
			args_0_isnull->   EqualTo(
			args_0_isnull->      ConvertTo(Int32,
			args_0_isnull->         LoadIndirect("NullableDatum", "isnull",
			args_0_isnull->            IndexAt(pNullableDatum,
			args_0_isnull->               LoadIndirect("FunctionCallInfoBaseData", "args",
			args_0_isnull->                  Load("fcinfo")),
			args_0_isnull->               ConstInt32(0))    )),
			args_0_isnull->      ConstInt32(1));

	IlBuilder *args_1_isnull = OrphanBuilder();
	OMR::JitBuilder::IlValue *hasnull_R =
			args_1_isnull->   EqualTo(
			args_1_isnull->      ConvertTo(Int32,
			args_1_isnull->         LoadIndirect("NullableDatum", "isnull",
			args_1_isnull->            IndexAt(pNullableDatum,
			args_1_isnull->               LoadIndirect("FunctionCallInfoBaseData", "args",
			args_1_isnull->                  Load("fcinfo")),
			args_1_isnull->               ConstInt32(1))    )),
			args_1_isnull->      ConstInt32(1));

	IlBuilder *null_true = NULL, *null_false = NULL;
	IfAnd(&null_true, &null_false, 2,
			MakeCondition(args_0_isnull, hasnull_L),
			MakeCondition(args_1_isnull, hasnull_R));
	{
		null_true->StoreAt(null_true->LoadAt(pDatum, null_true->Load("resvalue")), null_true->ConvertTo(pDat, null_true->ConstInt8(true)));
		null_true->StoreAt(null_true->LoadAt(pBool, null_true->Load("resnull")), null_true->ConstInt8(false));
	}
	{
		IlBuilder *else_args_0_isnull = null_false->OrphanBuilder();
		OMR::JitBuilder::IlValue *else_hasnull_L =
				else_args_0_isnull->   EqualTo(
				else_args_0_isnull->      ConvertTo(Int32,
				else_args_0_isnull->         LoadIndirect("NullableDatum", "isnull",
				else_args_0_isnull->            IndexAt(pNullableDatum,
				else_args_0_isnull->               LoadIndirect("FunctionCallInfoBaseData", "args",
				else_args_0_isnull->                  Load("fcinfo")),
				else_args_0_isnull->               ConstInt32(0))    )),
				else_args_0_isnull->      ConstInt32(1));

		IlBuilder *else_args_1_isnull = null_false->OrphanBuilder();
		OMR::JitBuilder::IlValue *else_hasnull_R =
				else_args_1_isnull->   EqualTo(
				else_args_1_isnull->      ConvertTo(Int32,
				else_args_1_isnull->         LoadIndirect("NullableDatum", "isnull",
				else_args_1_isnull->            IndexAt(pNullableDatum,
				else_args_1_isnull->               LoadIndirect("FunctionCallInfoBaseData", "args",
				else_args_1_isnull->                  Load("fcinfo")),
				else_args_1_isnull->               ConstInt32(1))    )),
				else_args_1_isnull->      ConstInt32(1));

		IlBuilder *else_null_true = NULL, *else_null_false = NULL;

		null_false->IfOr(&else_null_true, &else_null_false, 2,
		null_false->	MakeCondition(else_args_0_isnull, else_hasnull_L),
		null_false->	MakeCondition(else_args_1_isnull, else_hasnull_R));
		{
			else_null_true->StoreAt(else_null_true->LoadAt(pDatum, else_null_true->Load("resvalue")), else_null_true->ConvertTo(pDat, else_null_true->ConstInt8(false)));
			else_null_true->StoreAt(else_null_true->LoadAt(pBool, else_null_true->Load("resnull")), else_null_true->ConstInt8(false));
		}
		{
			else_null_false->StoreIndirect("FunctionCallInfoBaseData", "isnull", else_null_false->Load("fcinfo"), else_null_false->ConstInt8(false));
			else_null_false->StoreAt(else_null_false->LoadAt(pDatum, else_null_false->Load("resvalue")), else_null_false->Load("eqresult"));
			else_null_false->StoreAt(else_null_false->LoadAt(pBool, else_null_false->Load("resnull")),
			else_null_false->	LoadIndirect("FunctionCallInfoBaseData", "isnull",
			else_null_false->   	Load("fcinfo")));
		}

	}

	Return(ConstInt32(0));
	return true;

   }
/*
 *
 *
 *
 *
 * */




//EEOP VAR
class EEOP_VAR_class : public OMR::JitBuilder::MethodBuilder
{
protected:
	OMR::JitBuilder::IlType *pTupleTableSlot;
	OMR::JitBuilder::IlType *pBool;
	OMR::JitBuilder::IlType *pDatum;
	OMR::JitBuilder::IlType *pDat;
	OMR::JitBuilder::IlType *pbool;
	OMR::JitBuilder::IlType *bool_type;
	OMR::JitBuilder::IlType *Datum_type;
public:
	EEOP_VAR_class(OMR::JitBuilder::TypeDictionary *);
	virtual bool buildIL();
};
class StructTypeDictionary2 : public OMR::JitBuilder::TypeDictionary
   {
   public:

   StructTypeDictionary2() :
      OMR::JitBuilder::TypeDictionary()
      {
   	   /****Declare TupleTableSlot*********/
   	   DEFINE_STRUCT(TupleTableSlot);

   	   DEFINE_FIELD(TupleTableSlot, tts_values, toIlType<Datum *>());
   	   DEFINE_FIELD(TupleTableSlot, tts_isnull, toIlType<bool *>());

   	   CLOSE_STRUCT(TupleTableSlot);
      }
   };

EEOP_VAR_class::EEOP_VAR_class(OMR::JitBuilder::TypeDictionary *types)
   : OMR::JitBuilder::MethodBuilder(types)
   {
   DefineLine(LINETOSTR(__LINE__));
   DefineFile(__FILE__);

   DefineName("EEOP_VAR");

   pTupleTableSlot = types->PointerTo((char *)"TupleTableSlot");

   pbool = types->toIlType<bool *>();
   pBool = types->toIlType<bool **>();

   pDatum = types->toIlType<Datum **>();
   pDat = types->toIlType<Datum *>();

   bool_type = types->toIlType<bool>();
   Datum_type = types->toIlType<Datum>();

   DefineParameter("attnum",    Int32);
   DefineParameter("slot",     pTupleTableSlot);
   /*DefineParameter("d",  Datum_type);
   DefineParameter("b",  bool_type);*/
   DefineParameter("resnull",  pBool);
   DefineParameter("resvalue",  pDatum);

   DefineReturnType(NoType);
   }

bool
EEOP_VAR_class::buildIL()
   {
	Store("test_var", ConstInt32(0));
	//*op->resvalue = slot->tts_values[attnum];
	//StoreAt(LoadAt(pDatum, Load("resvalue")), IndexAt(pDat, LoadIndirect("TupleTableSlot", "tts_values", Load("slot")), ConvertTo(Int32, Load("attnum")))  );
	//StoreAt(LoadAt(pDatum, Load("resvalue")), ConvertTo(Datum_type, Load("d")));

	//*op->resnull = slot->tts_isnull[attnum];
	//StoreAt(LoadAt(pBool, Load("resnull")), IndexAt(pbool, LoadIndirect("TupleTableSlot", "tts_isnull", Load("slot")), ConvertTo(Int32, Load("attnum")))   );
	//StoreAt(LoadAt(pBool, Load("resnull")), ConvertTo(bool_type, Load("b")));

	return true;

   }

class EEOP_ASSIGN_VAR_class : public OMR::JitBuilder::MethodBuilder
{
protected:
	OMR::JitBuilder::IlType *pTupleTableSlot;
	OMR::JitBuilder::IlType *bool_type;
	OMR::JitBuilder::IlType *Datum_type;
	OMR::JitBuilder::IlType *pbool;
	OMR::JitBuilder::IlType *pDatum;
public:
	EEOP_ASSIGN_VAR_class(OMR::JitBuilder::TypeDictionary *);
	virtual bool buildIL();
};

EEOP_ASSIGN_VAR_class::EEOP_ASSIGN_VAR_class(OMR::JitBuilder::TypeDictionary *types)
   : OMR::JitBuilder::MethodBuilder(types)
   {
   DefineLine(LINETOSTR(__LINE__));
   DefineFile(__FILE__);

   DefineName("EEOP_ASSIGN_VAR_OMR");

   pbool = types->toIlType<bool *>();
   pDatum = types->toIlType<Datum *>();
   pTupleTableSlot = types->PointerTo((char *)"TupleTableSlot");
   bool_type = types->toIlType<bool>();
   Datum_type = types->toIlType<Datum>();

   /*DefineParameter("res_dat",     pDatum);
   DefineParameter("res_bool",    pbool);
   DefineParameter("slot_dat",    Datum_type);
   DefineParameter("slot_bool",   bool_type);*/

   DefineParameter("resultnum",     Int32);
   DefineParameter("resultslot",    pTupleTableSlot);
   DefineParameter("slot_dat",    	Datum_type);
   DefineParameter("slot_bool",     bool_type);

   DefineReturnType(Int32);

   }

bool
EEOP_ASSIGN_VAR_class::buildIL()
{
	/*LoadAt(pDatum, LoadIndirect("TupleTableSlot", "tts_values", Load("slot")));
	LoadAt(pDatum, LoadIndirect("TupleTableSlot", "tts_isnull", Load("slot")));*/
	/*Store("val", 	  IndexAt(pDatum, Load("slot_dat"), ConvertTo(Int32, Load("attnum"))));
	Store("bool_val", IndexAt(pbool,  Load("slot_bool"),  ConvertTo(Int32, Load("attnum"))));*/

	//resultslot->tts_values[resultnum] = slot->tts_values[attnum];
	/*StoreAt(Load("res_dat"),
			ConvertTo(Datum_type, Load("slot_dat")));

	//resultslot->tts_isnull[resultnum] = slot->tts_isnull[attnum];
	StoreAt( Load("res_bool"),
			ConvertTo(bool_type, Load("slot_bool")));*/

	StoreAt(IndexAt(pDatum, LoadIndirect("TupleTableSlot", "tts_values", Load("resultslot")), ConvertTo(Int32, Load("resultnum"))),
			ConvertTo(Datum_type, Load("slot_dat")));

	StoreAt(IndexAt(pbool, LoadIndirect("TupleTableSlot", "tts_isnull", Load("resultslot")), ConvertTo(Int32, Load("resultnum"))),
			ConvertTo(bool_type, Load("slot_bool")));

	Return(ConstInt32(0));
	return true;
}

/*
 *
 * EEOP_AGGREF
 *
 * */

class EEOP_AGGREF_class : public OMR::JitBuilder::MethodBuilder
{
protected:
	OMR::JitBuilder::IlType *pExprContext;
	OMR::JitBuilder::IlType *pInt32;
	OMR::JitBuilder::IlType *pBool;
	OMR::JitBuilder::IlType *pDatum;
	OMR::JitBuilder::IlType *pDat;
	OMR::JitBuilder::IlType *pDatPtr;
	OMR::JitBuilder::IlType *pBoolPtr;
public:
	EEOP_AGGREF_class(OMR::JitBuilder::TypeDictionary *);
	virtual bool buildIL();
};

class StructTypeDictionary4 : public OMR::JitBuilder::TypeDictionary
   {
   public:

   StructTypeDictionary4() :
      OMR::JitBuilder::TypeDictionary()
      {
	   	  DEFINE_STRUCT(ExprContext);

	   	  DEFINE_FIELD(ExprContext, ecxt_aggvalues, toIlType<Datum *>());
	   	  DEFINE_FIELD(ExprContext, ecxt_aggnulls,  toIlType<bool *>());

	   	  CLOSE_STRUCT(ExprContext);
      }
   };

EEOP_AGGREF_class::EEOP_AGGREF_class(OMR::JitBuilder::TypeDictionary *types)
   : OMR::JitBuilder::MethodBuilder(types)
   {
   DefineLine(LINETOSTR(__LINE__));
   DefineFile(__FILE__);

   DefineName("EEOP_AGGREF_method");

   pInt32 = types->PointerTo(Int32);

   pExprContext = types->PointerTo((char *)"ExprContext");

   pBool = types->toIlType<bool **>();

   pDatum = types->toIlType<Datum **>();
   pDat = types->toIlType<Datum>();
   pDatPtr = types->toIlType<Datum *>();
   pBoolPtr = types->toIlType<bool *>();

   DefineParameter("resnull",   pBool);
   DefineParameter("resvalue",  pDatum);
   DefineParameter("ecxt_aggvalues",     pDat);
   DefineParameter("ecxt_aggnulls",  types->toIlType<bool>());

   DefineReturnType(Int32);
   }

bool
EEOP_AGGREF_class::buildIL()
   {

	StoreAt(LoadAt(pDatum, Load("resvalue")), Load("ecxt_aggvalues"));
	StoreAt(LoadAt(pBool,  Load("resnull")),  Load("ecxt_aggnulls"));

	Return(ConstInt32(0));
	return true;

   }


/*
 *
 * EEOP_ASSIGN_TMP_MAKE_RO
 *
 * */

class EEOP_ASSIGN_TMP_MAKE_RO_class : public OMR::JitBuilder::MethodBuilder
{
protected:
	OMR::JitBuilder::IlType *pExprState;
	OMR::JitBuilder::IlType *pTupleTableSlot;
	OMR::JitBuilder::IlType *pInt32;
	OMR::JitBuilder::IlType *pBool;
	OMR::JitBuilder::IlType *pDatum;
	OMR::JitBuilder::IlType *pDat;
	OMR::JitBuilder::IlType *pDatPtr;
	OMR::JitBuilder::IlType *pBoolPtr;
public:
	EEOP_ASSIGN_TMP_MAKE_RO_class(OMR::JitBuilder::TypeDictionary *);
	virtual bool buildIL();
};

class StructTypeDictionary5 : public OMR::JitBuilder::TypeDictionary
   {
   public:

   StructTypeDictionary5() :
      OMR::JitBuilder::TypeDictionary()
      {
   	      DEFINE_STRUCT(TupleTableSlot);
   	   	  DEFINE_FIELD(TupleTableSlot, tts_values, toIlType<Datum *>());
   	   	  DEFINE_FIELD(TupleTableSlot, tts_isnull, PointerTo(Int32));
   	   	  CLOSE_STRUCT(TupleTableSlot);

	   	  DEFINE_STRUCT(ExprState);
	   	  DEFINE_FIELD(ExprState, resnull, toIlType<bool>());
	   	  DEFINE_FIELD(ExprState, resvalue,  toIlType<Datum>());
	   	  CLOSE_STRUCT(ExprState);
      }
   };

EEOP_ASSIGN_TMP_MAKE_RO_class::EEOP_ASSIGN_TMP_MAKE_RO_class(OMR::JitBuilder::TypeDictionary *types)
   : OMR::JitBuilder::MethodBuilder(types)
   {
   DefineLine(LINETOSTR(__LINE__));
   DefineFile(__FILE__);

   DefineName("EEOP_ASSIGN_TMP_MAKE_RO_method");

   pInt32 = types->PointerTo(Int32);

   pExprState = types->PointerTo((char *)"ExprState");
   pTupleTableSlot = types->PointerTo((char *)"TupleTableSlot");

   pBool = types->toIlType<bool **>();

   pDatum = types->toIlType<Datum **>();
   pDat = types->toIlType<Datum>();
   pDatPtr = types->toIlType<Datum *>();
   pBoolPtr = types->toIlType<bool *>();

   DefineParameter("resultnum",   Int32);
   DefineParameter("resultslot",  pTupleTableSlot);
   DefineParameter("state",       pExprState);

   DefineFunction((char *)"MakeExpandedObjectReadOnlyInternal_func",
                  (char *)__FILE__,
                  (char *)MakeExpandedObjectReadOnlyInternal_func_LINE,
                  (void *)&MakeExpandedObjectReadOnlyInternal_func,
                  pDat,
                  1,
				  pDat);

   DefineReturnType(Int32);
   }

bool
EEOP_ASSIGN_TMP_MAKE_RO_class::buildIL()
   {

	/*resultslot->tts_isnull[resultnum] = state->resnull;
	if (!resultslot->tts_isnull[resultnum])
		resultslot->tts_values[resultnum] =
			MakeExpandedObjectReadOnlyInternal(state->resvalue);
	else
		resultslot->tts_values[resultnum] = state->resvalue;*/

	StoreAt(IndexAt(pBoolPtr, LoadIndirect("TupleTableSlot", "tts_isnull", Load("resultslot")), ConvertTo(Int32, Load("resultnum"))),
			LoadIndirect("ExprState", "resnull", Load("state")));

	OMR::JitBuilder::IlBuilder *isnull = NULL;
	OMR::JitBuilder::IlBuilder *isnullelse = NULL;
	IfThenElse(&isnull, &isnullelse,
			NotEqualTo(
					LoadAt(pBoolPtr, IndexAt(pBoolPtr,
					   LoadIndirect("TupleTableSlot", "tts_isnull",
					      Load("resultslot")),
					   ConvertTo(Int32,
					      Load("resultnum")))),
			        ConstInt8(true)));

	isnull->StoreAt(
	isnull->   IndexAt(pDatPtr,
	isnull->      LoadIndirect("TupleTableSlot", "tts_values",
	isnull->         Load("resultslot")),
	isnull->      ConvertTo(Int32,
	isnull->         Load("resultnum"))),
	isnull->   Call("MakeExpandedObjectReadOnlyInternal_func", 1,
	isnull->      LoadIndirect("ExprState", "resvalue",
	isnull->         Load("state"))));

	isnullelse->StoreAt(
	isnullelse->   IndexAt(pDatPtr,
	isnullelse->      LoadIndirect("TupleTableSlot", "tts_values",
	isnullelse->         Load("resultslot")),
	isnullelse->      ConvertTo(Int32,
	isnullelse->         Load("resultnum"))),
	isnullelse->   LoadIndirect("ExprState", "resvalue",
	isnullelse->      Load("state")));



	Return(ConstInt32(0));
	return true;

   }
/*
 *
 * end
 *
 * */


/*
 *
 * float8_pl
 *
 * */

class float8_pl_class : public OMR::JitBuilder::MethodBuilder
{
protected:
	OMR::JitBuilder::IlType *pFloat;
public:
	float8_pl_class(OMR::JitBuilder::TypeDictionary *);
	virtual bool buildIL();
};

float8_pl_class::float8_pl_class(OMR::JitBuilder::TypeDictionary *types)
   : OMR::JitBuilder::MethodBuilder(types)
   {
   DefineLine(LINETOSTR(__LINE__));
   DefineFile(__FILE__);

   DefineName("float8_pl_method");

   pFloat = types->PointerTo(Float);

   DefineParameter("arg1",   Float);
   DefineParameter("arg2",   Float);

   DefineReturnType(Float);
   }

bool
float8_pl_class::buildIL()
   {

	Return(Add(Load("arg1"), Load("arg2")));
	return true;

   }

/*
 *
 * end
 *
 * */

extern "C" {
PG_MODULE_MAGIC;

/*function to compile tuple deformation Jit code*/
OMRJIT_slot_deformFunctionType * omr_compile(){

	StructTypeDictionary joinmethodTypes;

	slot_compile_deform method(&joinmethodTypes);
	void *entry=0;
	int32_t rc = compileMethodBuilder(&method, &entry);

	if (rc != 0)
	{

		elog(INFO, "FAIL: compilation error %d\n", rc);
	   exit(-2);
	}
	/*slot_deform = (OMRJIT_slot_deformFunctionType *)entry;*/
	return (OMRJIT_slot_deformFunctionType *)entry;

}

eval_expr_qual_FunctionType * EEOP_Qual_compile_func(){

	OMR::JitBuilder::TypeDictionary types;
	EEOP_QUAL_class method(&types);
	void *entry=0;
	int32_t rc = compileMethodBuilder(&method, &entry);

	if (rc != 0)
	{
		elog(INFO, "FAIL: compilation error %d\n", rc);
	    exit(-2);
	}
	/*qual_FunctionType = (eval_expr_qual_FunctionType *)entry;*/
	return (eval_expr_qual_FunctionType *)entry;

}

EEOP_FUNCEXPR_STRICT_FunctionType * EEOP_FUNCEXPR_STRICT_compile_func(){
	StructTypeDictionary1 types;
	EEOP_FUNCEXPR_STRICT_class method(&types);
	void *entry=0;
	int32_t rc = compileMethodBuilder(&method, &entry);

	if (rc != 0)
	{

	   elog(INFO, "FAIL: compilation error %d\n", rc);
	   exit(-2);
	}
	return (EEOP_FUNCEXPR_STRICT_FunctionType *)entry;
	//FUNCEXPR_STRICT = (EEOP_FUNCEXPR_STRICT_FunctionType *)entry;

}

EEOP_NOT_DISTINCT_FunctionType * EEOP_NOT_DISTINCT_compile_func(){

	StructTypeDictionary3 types;
	EEOP_NOT_DISTINCT_class method(&types);
	void *entry=0;
	int32_t rc = compileMethodBuilder(&method, &entry);

	if (rc != 0)
	{

	   elog(INFO, "FAIL: compilation error %d\n", rc);
	   exit(-2);
	}
	return (EEOP_NOT_DISTINCT_FunctionType *)entry;

}


EEOP_VAR_FunctionType * EEOP_VAR_compile_func(){
	StructTypeDictionary2 types;
	EEOP_VAR_class method(&types);
	void *entry=0;
	int32_t rc = compileMethodBuilder(&method, &entry);
	if (rc != 0)
	{
	   elog(INFO, "FAIL: compilation error %d\n", rc);
	   exit(-2);
	}
	return (EEOP_VAR_FunctionType *)entry;

}


EEOP_ASSIGN_VAR_FunctionType * EEOP_ASSIGN_VAR_compile_func(){
	StructTypeDictionary2 types;
	EEOP_ASSIGN_VAR_class method(&types);
	void *entry=0;
	int32_t rc = compileMethodBuilder(&method, &entry);
	if (rc != 0)
	{
	   elog(INFO, "FAIL: compilation error %d\n", rc);
	   exit(-2);
	}
	return (EEOP_ASSIGN_VAR_FunctionType *)entry;

}

EEOP_AGGREF_FunctionType * EEOP_AGGREF_compile_func(){
	StructTypeDictionary4 types;
	EEOP_AGGREF_class method(&types);
	void *entry=0;
	int32_t rc = compileMethodBuilder(&method, &entry);
	if (rc != 0)
	{
	   elog(INFO, "FAIL: compilation error %d\n", rc);
	   exit(-2);
	}
	return (EEOP_AGGREF_FunctionType *)entry;

}

EEOP_ASSIGN_TMP_MAKE_RO_FunctionType * EEOP_ASSIGN_TMP_MAKE_RO_compile_func(){
	StructTypeDictionary5 types;
	EEOP_ASSIGN_TMP_MAKE_RO_class method(&types);
	void *entry=0;
	int32_t rc = compileMethodBuilder(&method, &entry);
	if (rc != 0)
	{
	   elog(INFO, "FAIL: compilation error %d\n", rc);
	   exit(-2);
	}
	return (EEOP_ASSIGN_TMP_MAKE_RO_FunctionType *)entry;

}

float8_pl_FunctionType * float8_add_func(){

	OMR::JitBuilder::TypeDictionary types;
	float8_pl_class method(&types);
	void *entry=0;
	int32_t rc = compileMethodBuilder(&method, &entry);
	if (rc != 0)
	{
	   elog(INFO, "FAIL: compilation error %d\n", rc);
	   exit(-2);
	}
	return (float8_pl_FunctionType *)entry;

}

/*This function was used earlier for doing the compilation and invoking.
 * We don't need it now and can be used for testing purposes*/
void omr_tuple_deform(int32_t natts, TupleTableSlot *slot, HeapTuple tuple, uint32 *offp)
{

	slot_deform(natts, slot, tuple, offp);;
}

}















