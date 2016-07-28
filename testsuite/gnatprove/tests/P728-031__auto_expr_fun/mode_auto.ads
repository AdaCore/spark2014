package Mode_Auto is
   type My_Private is private;

   function Private_Expr_Fun (P : My_Private) return Boolean;
private
   type My_Access is access all Integer;

   type My_Private is record
      F : Boolean;
      G : My_Access;
   end record;

   function Private_Expr_Fun (P : My_Private) return Boolean is (P.F);
end Mode_Auto;
