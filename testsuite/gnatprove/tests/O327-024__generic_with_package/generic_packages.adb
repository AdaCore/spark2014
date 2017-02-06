package body Generic_Packages is
   package body Gen_Sum with SPARK_Mode => Off is
      function Sum (A : Element_Array) return Element is
         Res : Element := 0;
      begin
         for I in A'Range loop
            if (Res > 0 and then Element'Last - Res >= A (I))
              or else Element'First - Res <= A (I)
            then
               Res := Element_Add.Add (Res, A (I));
            end if;
         end loop;
         return Res;
      end Sum;
      type Bad is access Element;
   end Gen_Sum;
end Generic_Packages;
