procedure Main with SPARK_Mode is
   generic
   package MakeAbstractType is
      type Result is private;
   private
      pragma SPARK_Mode(Off);
      type Result is null record;
   end MakeAbstractType;
   package A is new MakeAbstractType;
   subtype T is A.Result;
   function "="(X, Y : T) return Boolean renames A."=";
   procedure Refl(X : T) with Post => X = X;
   procedure Refl(X : T) is null;
begin
   null;
end;
