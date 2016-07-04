package body Procedure_On_Protected with SPARK_Mode is
   procedure Init (X : out R) is
   begin
      X.F := 0;
   end Init;

   protected body Obj is
      procedure Do_Init is
      begin
         Init (C);
      end Do_Init;
   end Obj;

end Procedure_On_Protected;
