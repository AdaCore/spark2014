
--  Test accounting of effects of functions in structural variant analysis

procedure Structural_Variant with SPARK_Mode is
   type Cell;
   type List is access Cell;
   type Cell is record
      Head : Integer;
      Tail : List;
   end record;
   function Update (X : in out Cell) return Boolean with Side_Effects, Import, Global => null, Always_Terminates => True;
   procedure Test (X : List) with Always_Terminates => True, Subprogram_Variant => (Structural => X);
   procedure Test (X : List) is
      Y : access Cell := X;
   begin
      if Y /= null then
         if Update (Y.all) then
            Test (Y.Tail); --@SUBPROGRAM_VARIANT:FAIL
         end if;
      end if;
   end Test;

   function Cut_Suffix (X : List; Marker : Integer) return Boolean
     with Side_Effects, Global => null, Subprogram_Variant => (Structural => X);
   function Cut_Suffix (X : List; Marker : Integer) return Boolean is
   begin
      if X = null then
         return False;
      elsif X.Head = Marker then
         X.Tail := null;
         return True;
      else
         return Cut_Suffix (X.Tail, Marker); --@SUBPROGRAM_VARIANT:PASS
      end if;
   end Cut_Suffix;

begin
   null;
end Structural_Variant;
