--  Coverage example

procedure Bar with SPARK_Mode is
   type Cell;
   type List is access Cell;
   type Cell is record
      Next : List;
   end record;

   function Finite (L : access constant Cell) return Boolean
     with Subprogram_Variant => (Structural => L),
     Post => Finite'Result = (if L /= null then Finite (L.Next));
   function Finite (L : access constant Cell) return Boolean is
   begin
      return (if L /= null then Finite (L.Next));
   end Finite;
begin
   null;
end Bar;
