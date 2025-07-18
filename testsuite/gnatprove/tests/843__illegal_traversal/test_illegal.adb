procedure Test_Illegal with SPARK_Mode is

   --  Check that IN OUT parameters are still rejected when not the first param of a traversal function

   type Int_Acc is access Integer;

   function F_1 (X : aliased in out Integer) return not null access Integer with Import;

   function F_2 (Y : Integer; X : aliased in out Integer) return not null access Integer with Import;

   function F_3 (X : aliased in out Integer) return not null Int_Acc with Import;
begin
   null;
end;
