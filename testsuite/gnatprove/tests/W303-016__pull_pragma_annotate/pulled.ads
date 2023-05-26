with Generics; use Generics;

package Pulled with SPARK_Mode is
   
   
   X : Integer := 0;

   -- Correctly pull pragma from parent packages.
   package A with Annotate => (GNATprove, Always_Return) is
      package B is
         package C is
            procedure Work with Global => (In_Out => X);
         end C;
      end B;
   end A;

   procedure Terminating_Generic_Instance is new Terminating_Generic (0);
   
   procedure Terminating_Instance is new Terminating_Instance_Builder (0)
     with Annotate => (GNATprove, Always_Return);
   procedure Terminating_Instance_2 is new Terminating_Instance_Builder (1);
   pragma Annotate (GNATprove, Always_Return, Terminating_Instance_2);
   
end Pulled;
