package Extended_Returns is
   type Record_T (Discr : Natural := 0) is
      record
         A : Integer;
         case Discr is
            when 0 =>
               B : Integer;
            when 1 =>
               C, D : Integer;
            when others =>
               null;
         end case;
      end record;

   function Init (Discr    : Integer;
                  Init_Val : Natural) return Record_T
      with Post => Init'Result.A = Init_Val;
end Extended_Returns;
