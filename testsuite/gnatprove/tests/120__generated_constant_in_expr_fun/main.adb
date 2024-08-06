procedure Main
  with
    SPARK_Mode => On
is
   type Nat_Array is array (Positive range <>) of Natural;
    type Info_Type (Size : Natural) is record
        Content : Nat_Array (1 .. Size);
    end record;

   V : Natural;

   function Size return Natural is (V);

   function Read return Nat_Array with
     Import,
     Annotate => (GNATprove, Always_Return),
     Post => Read'Result'First = 1 and Read'Result'Last = Size,
     Global => V;

   function Get_Info return Info_Type
   is
     (Size    => Size,
      Content => Read);
begin
   V := 0;
   declare
      I0 : constant Info_Type := Get_Info;
   begin
      V := 1;
      declare
         I1 : constant Info_Type := Get_Info;
      begin
         pragma Assert (False); --@ASSERT:FAIL
      end;
   end;
end Main;
