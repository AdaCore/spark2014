with C413005P;

procedure X with SPARK_Mode is

   function Func return access C413005P.TP is
   begin
      return null;
   end Func;

   procedure Func_Set (Value : in Integer) renames Func.Set;
   --  renaming-as-spec

begin
   null;
end;
