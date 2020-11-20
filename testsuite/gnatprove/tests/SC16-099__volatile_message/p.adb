package body P
  with Refined_State => (State => (Ext_Value, Local_Value))
is
   --  Two tests. First is simple detection of volatile variabels
   --  used by a nonvolatile function. In the second we
   --  deliberately create a deeply nested record type where
   --  a field is externally writable. The function to "get"
   --  this field is therefore volatile as it accesses external
   --  state.

   Ext_Value : Natural := 0
   with
      Atomic,
      Async_Writers;

   type Innermost is record
     C: Natural :=0;
     D: Integer :=0;
   end record;

   type Middle is record
      In1: Innermost;
      In2: Innermost;
   end record;
   type Outer is record
      Mid : Middle;
   end record;

   Local_Value : Outer;

   function F return Integer is
      X1 : Integer := X;  --  message (1)
      Y1 : Integer := Y;  --  message (2)
   begin
      return X1 + Y1;
   end;

   procedure Update
   is
   begin
      Local_Value.Mid.In1.C := Ext_Value;
   end Update;

   function Get return Natural is (Local_Value.Mid.In1.C);
end;
