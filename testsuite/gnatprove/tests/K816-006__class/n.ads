package N is pragma SPARK_Mode (Off);
   type R is abstract tagged null record;

   procedure O (X : in out R) is abstract;
end N;
