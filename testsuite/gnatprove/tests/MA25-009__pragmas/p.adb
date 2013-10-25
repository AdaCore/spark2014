pragma SPARK_Mode;
pragma Restrictions (No_Recursion);
pragma Restriction_Warnings (No_Floating_Point);
pragma Profile (Ravenscar);

procedure P is
   pragma Warnings (Off);
   I : Integer := 0;
   pragma Warnings (On);
   pragma Inspection_Point (I);
   pragma Linker_Options ("-lx");
   pragma List (Off);
   pragma Optimize (Time);
   pragma Page;
   pragma Reviewable;

begin
   null;
end P;
