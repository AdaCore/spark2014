procedure Test_Access with SPARK_Mode is
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      V : Integer;
      N : List;
   end record;

   function Find_Max
     (L : not null access constant List_Cell)
      return not null access constant List_Cell
   is
      C : access constant List_Cell := L;
   begin
      loop
         pragma Loop_Invariant (C /= null);
         declare
            Prec : access constant List_Cell := C;
            Max  : constant Integer := C.V;
         begin
            while C /= null and then C.V <= Max loop
               C := C.N;
            end loop;
            if C = null then
               return Prec;
            end if;
         end;
      end loop;
   end Find_Max;

begin
   null;
end Test_Access;
