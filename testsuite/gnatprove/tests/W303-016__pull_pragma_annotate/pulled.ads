with Generics; use Generics;

package Pulled with SPARK_Mode is


   X : Integer := 0;

   -- Correctly pull pragma from parent packages.
   package A with Always_Terminates is
      package B is
         package C is
            procedure Work with Global => (In_Out => X);
         end C;
      end B;
   end A;

   procedure Terminating_Generic_Instance is new Terminating_Generic (0);

   package I with Always_Terminates is
      procedure Terminating_Instance is new Terminating_Instance_Builder (0);
      procedure Terminating_Instance_2 is new Terminating_Instance_Builder (1);
   end;
   procedure Terminating_Instance renames I.Terminating_Instance;
   procedure Terminating_Instance_2 renames I.Terminating_Instance_2;

end Pulled;
