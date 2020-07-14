package body Spec with SPARK_Mode is
   procedure Z3 (X : in out Integer) is
   begin
      if X < Integer'Last then
         X := X + 1;
      end if;
   end Z3;
end Spec;
