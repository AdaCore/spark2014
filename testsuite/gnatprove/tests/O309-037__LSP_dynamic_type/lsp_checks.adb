procedure LSP_Checks (C : Natural) with SPARK_Mode is

   package Nested is
      subtype My_Natural is Natural range 0 .. C;

      type Root is tagged record
         F1 : My_Natural;
      end record;

      function Root_Pre_Class (R : Root'Class; G : My_Natural) return Boolean is
        (C - G >= R.F1);
      function Root_Post_Class (R : Root'Class; G, G_Old : My_Natural) return Boolean is
        (if C - G_Old >= R.F1 then G = G_Old + R.F1);

      Glob : My_Natural := 0;

      procedure Do_Something (R : Root) with
        Pre'Class => Root_Pre_Class (R, Glob),
        Post'Class => Root_Post_Class (R, Glob, Glob'Old);

      type Child is new Root with record
         F2 : My_Natural;
      end record;

      function Child_Pre_Class (R : Child'Class; G : My_Natural) return Boolean is
        (C - G >= R.F1 or C - G >= R.F2);
      function Child_Pre (R : Child'Class; G : My_Natural) return Boolean is
        (True);

      function Child_Post_Class (R : Child'Class; G, G_Old : My_Natural) return Boolean is
        (if C - G_Old >= R.F1 then G = G_Old + R.F1
         elsif C - G_Old >= R.F2 then G = G_Old + R.F2);
      function Child_Post (R : Child'Class; G, G_Old : My_Natural) return Boolean is
        (if C - G_Old >= R.F1 then G = G_Old + R.F1
         elsif C - G_Old >= R.F2 then G = G_Old + R.F2
         else G = G_Old);

      procedure Do_Something (R : Child) with

        Post => Child_Post (R, Glob, Glob'Old),
        Pre'Class => Child_Pre_Class (R, Glob),
        Post'Class => Child_Post_Class (R, Glob, Glob'Old);
   end Nested;

   package body Nested is
      procedure Do_Something (R : Root) is
      begin
         Glob := Glob + R.F1;
      end Do_Something;

      procedure Do_Something (R : Child)is
      begin
         if C - Glob >= R.F1 then
            Glob := Glob + R.F1;
         elsif C - Glob >= R.F2 then
            Glob := Glob + R.F2;
         end if;
      end Do_Something;
   end Nested;

   use Nested;

   R1 : Root'Class := Root'(F1 => 0);
   R2 : Root'Class := Child'(F1 => C, F2 => 0);
begin
   Nested.Glob := 0;
   Do_Something (R1);
   pragma Assert (Glob = 0);
   Do_Something (R2);
   pragma Assert (Glob = C);
end;
