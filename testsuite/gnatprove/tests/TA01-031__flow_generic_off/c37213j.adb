procedure C37213J with
   SPARK_Mode => off
is
   generic
      type CONS is private;
   package OBJ_CHK is
   end OBJ_CHK;

   package body OBJ_CHK is
      X : CONS;

      function VALUE return CONS is
      begin
         return X;
      end VALUE;
   begin
      if X /= VALUE then
         null;
      end if;
   end OBJ_CHK;
begin
   --  With SPARK_Mode => Off we will use frontend cross-references to get the
   --  immediate callees of this routine. They wrongly include VALUE even
   --  though its enclosing generic unit is not even instantiated.
   null;
end C37213J;
