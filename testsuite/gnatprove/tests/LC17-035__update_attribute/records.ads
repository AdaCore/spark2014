with Types;       use Types;

package Records is

   pragma SPARK_Mode (Off);

   ----------------------------------------------------------------------------
   -- 'Update Record tests
   ----------------------------------------------------------------------------

   --  aggregate reference test, to compare Why3 models
   procedure P1 (R: in out Rec; New_Data: in Integer)
     with Post => R = Rec'(S1 => 3, S2 => New_Data, S3 => 4);

   --  single record component update
   procedure P2(R: in out Rec; New_Data: in Integer)
     with Post => R = R'Old'Update(S2 => New_Data);

   --  several but not all components update
   procedure P3(R: in out Rec; New_Data: in Integer; New_Data_2: in My_Range)
     with Post => R = R'Old'Update(S2 => New_Data, S3 => New_Data_2);

   --  all components update
   procedure P4 (R: in out Rec; New_Data: in Integer)
     with Post => R = R'Old'Update(S1 => 10, S2 => New_Data, S3 => 10);

   --  inc/decrement components, w/o precondition, overflow checks should fail
   procedure P5(R: in out Rec)
     with Post => R = R'Old'Update(S1 => R'Old.S1 + 1,
                                   S3 => R'Old.S3 - 1);

   --  inc/decrement components, w precondition
   procedure P6(R: in out Rec)
     with Pre  => R.S1 < Integer'Last and
                  R.S3 > My_Range'First,
          Post => R = R'Old'Update(S1 => R'Old.S1 + 1,
                                   S3 => R'Old.S3 - 1);

   --  aggregate, multiple choices, one association
   procedure P7(R: in out Rec);
--   with Post => R = Rec'(S1 | S3 => 2, S2 => 3);

   --  update attribute, multiple choices, one association
   procedure P8(R: in out Rec);
   --  with Post => R = R'Old'Update(S1 | S3 => 2);

end Records;
