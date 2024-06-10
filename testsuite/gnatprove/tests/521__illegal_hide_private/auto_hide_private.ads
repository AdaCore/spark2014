pragma SPARK_Mode (Auto);

package Auto_Hide_Private is
   type My_Private is private;

   function Private_Expr_Fun (P : My_Private) return Boolean;
private
   pragma Annotate (GNATprove, Hide_Info, "Private_Part", Auto_Hide_Private);
   type My_Access is access all Integer;

   type My_Private is record
      F : Boolean;
      G : My_Access;
   end record;

   function Private_Expr_Fun (P : My_Private) return Boolean is (P.F);
end Auto_Hide_Private;
