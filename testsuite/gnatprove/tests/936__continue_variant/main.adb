pragma Extensions_Allowed (All_Extensions);
procedure Main with SPARK_Mode is
   function Random (X : Integer) return Boolean
     with Import, Global => null;
   type Cell;
   type Tree is access Cell;
   type Cell is record
      V : Integer;
      L : Tree;
      R : Tree;
   end record;
   procedure OK_1 (X : access Cell)
     with Subprogram_Variant => (Structural => X);
   procedure KO_1 (X : access Cell)
     with Subprogram_Variant => (Structural => X);
   procedure KO_2 (X : access Cell)
     with Subprogram_Variant => (Structural => X);
   procedure KO_3 (X : access Cell)
     with Subprogram_Variant => (Structural => X);

   procedure OK_1 (X : access Cell) is
      Y : access Cell := X;
   begin
      loop
         if Random (Y.V) then
            continue;
         else
            Y := Y.L;
         end if;
         OK_1 (Y); --@SUBPROGRAM_VARIANT:PASS
         exit;
      end loop;
   end OK_1;

   procedure KO_1 (X : access Cell) is
      Y : access Cell := X;
   begin
      loop
         if Random (Y.V) then
            Y.R := null;
            continue;
         else
            Y := Y.L;
         end if;
         KO_1 (Y);  --@SUBPROGRAM_VARIANT:FAIL
         exit;
      end loop;
   end KO_1;

   procedure KO_2 (X : access Cell) is
      Y : access Cell := X;
   begin
      loop
         if Random (Y.V) then
            continue when Random (Y.V+1);
         else
            Y := Y.L;
         end if;
         KO_2 (Y);  --@SUBPROGRAM_VARIANT:FAIL
         exit;
      end loop;
   end KO_2;

   procedure KO_3 (X : access Cell) is
      Y : access Cell := X;
   begin
      Outer: loop
         while Random (Y.V+1) loop
            continue Outer when Random (Y.V);
            Y := Y.L;
         end loop;
         exit when Random (Y.V);
         KO_3 (Y); --@SUBPROGRAM_VARIANT:FAIL
         exit;
      end loop Outer;
   end KO_3;

begin
   null;
end Main;
