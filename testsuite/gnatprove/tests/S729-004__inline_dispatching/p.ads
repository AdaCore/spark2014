package P with SPARK_Mode is

   type T is tagged null record;
   procedure Proc (Self : T; X : Boolean) is null;

   procedure Test;
end P;
