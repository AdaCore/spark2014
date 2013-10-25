pragma SPARK_Mode;

procedure P is
   pragma Warnings (Off);
   I : Integer := 0;
   pragma Warnings (On);
   pragma Inspection_Point (I);
   pragma Linker_Options ("-lx");

begin
   null;
end P;
