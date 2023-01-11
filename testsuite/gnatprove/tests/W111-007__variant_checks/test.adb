procedure Test with SPARK_Mode is

   type List_Cell; type List is access List_Cell;

   type List_Cell is record
      Value : Integer;
      Next  : List;
   end record;

   function Length (L : List) return Natural is (0) with
     Post => (if L /= null and then L.Next /= null
              then Length (L) >  -- @SUBPROGRAM_VARIANT:FAIL
                  Length (L.all.Next)),
    Subprogram_Variant => (Structural => L);

   function F (L :  List) return Boolean with
    Subprogram_Variant => (Structural => L),
     Post => F'Result;

   procedure P (L : in out List; B : Boolean := False) with
     Post => F (L),  -- @SUBPROGRAM_VARIANT:FAIL
     Subprogram_Variant => (Structural => L)
   is
   begin
      L := new List_Cell'(Value => 0, Next => L);
      if B then
         pragma Assert (F (L));  -- @SUBPROGRAM_VARIANT:FAIL
      end if;
   end P;

   function F (L :  List) return Boolean is
      V : List := null;
   begin
      P (V);  -- @SUBPROGRAM_VARIANT:FAIL
      return True;
   end F;

begin
   null;
end;
