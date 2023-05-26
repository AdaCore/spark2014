package body Pulled with SPARK_Mode => Off is

   package body A is
      package body B is
         package body C is
            procedure Work is
            begin
               while X <= 42 loop
                  X := X +36;
               end loop;
            end Work;
         end C;
      end B;
   end A;

end Pulled;
