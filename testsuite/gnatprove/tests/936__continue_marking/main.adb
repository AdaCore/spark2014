pragma Extensions_Allowed (All_Extensions);
procedure Main with SPARK_Mode is
   function Random_Ko return Boolean with Import, SPARK_Mode => Off;
   function Random_Ok return Boolean with Import, Global => null;
begin
   loop
      pragma Loop_Invariant (True);
      continue; -- OK
   end loop;
   loop
      continue; -- OK
      null;
   end loop;
   Outer0: loop
      loop
         continue Outer0; -- OK
      end loop;
   end loop Outer0;
   loop
      continue; -- KO
      pragma Loop_Invariant (True);
   end loop;
   Outer: loop
      loop
         continue Outer; -- KO
      end loop;
      pragma Loop_Invariant (True);
   end loop Outer;
   Outer2 : loop
      loop
         continue; -- OK
      end loop;
      pragma Loop_Invariant (True);
   end loop Outer2;
   Outer3: loop
      if Random_Ok then
         continue when Random_Ko;
      else
         loop
            continue Outer3 when Random_Ko;
         end loop;
      end if;
   end loop Outer3;
   Inner_To_Outer: loop
      loop
        loop
           continue Inner_To_Outer when Random_Ok; -- OK
           pragma Loop_Invariant (True);
        end loop;
        pragma Loop_Invariant (True);
      end loop;
   end loop Inner_To_Outer;
end Main;
