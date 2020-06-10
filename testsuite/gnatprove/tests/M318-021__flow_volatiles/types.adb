with System.Storage_Elements; use System.Storage_Elements;

package body Types
  with Refined_State => (State => (A,
                                   --  B,
                                   C,
                                   D,
                                   E))
is
   type Volatile_Integer is new Integer with Volatile;

   A : Volatile_Integer;

   --  type Illegal_Record_T is record
   --     X : Integer;
   --     Y : Volatile_Integer;
   --  end record;

   type Record_T is record
      X : Integer;
   end record with Volatile;

   --  B : Illegal_Record_T with Volatile, Async_Writers, Effective_Reads;

   C : Volatile_Integer with Async_Writers, Effective_Reads;

   D : Integer with Volatile;

   E : Record_T;

   --  We can't do this, thankfully (SPARK RM 7.1.3(4))
   --  VC : constant Record_T with Address => To_Address (16#deadbeef#);

   procedure Test_01 (R : in Record_T)
   is
   begin
      null;
   end Test_01;

   procedure Test_02 (R : out Record_T)
   is
   begin
      null;
   end Test_02;

   procedure Test_03 (R : in out Record_T)
   is
   begin
      null;
   end Test_03;

   procedure Test_04 (R : out Record_T;
                      X : out Integer)
   is
   begin
      X := R.X;  -- illegal
   end Test_04;

   procedure Test_05 (R : out Record_T;
                      X : out Integer)
   is
   begin
      R.X := 12;
      X := R.X;  -- illegal
   end Test_05;

end Types;
