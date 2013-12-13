package body Types
   with Refined_State => (State => (A, B, C))
is
   type Volatile_Integer is new Integer with Volatile;

   A : Volatile_Integer;

   type Illegal_Record_T is record
      X : Integer;
      Y : Volatile_Integer;
   end record;

   B : Illegal_Record_T with Volatile, Async_Writers, Effective_Reads;

   C : Volatile_Integer with Volatile, Async_Writers, Effective_Reads;

end Types;
