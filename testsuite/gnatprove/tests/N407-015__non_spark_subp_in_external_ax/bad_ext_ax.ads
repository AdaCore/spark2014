package Bad_Ext_Ax with SPARK_Mode is
   pragma Annotate (GNATprove, External_Axiomatization);

   type Rec (D1, D2 : Natural) is null record;
   type Bad_Type (D : Natural) is new Rec (D, D);

   function Bad_Func (X : in out Integer) return Boolean;

private
   pragma SPARK_Mode (Off);
end Bad_Ext_Ax;
