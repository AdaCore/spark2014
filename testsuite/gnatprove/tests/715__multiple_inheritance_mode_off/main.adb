procedure Main with SPARK_Mode is

   --  T_2 inherits P multiply since P comes from its (private) parent
   --  and the interface, while T_3 does not inherit P multiply since
   --  inheritance is 'joined' at parent T_2. However, these are invisible
   --  in SPARK, so only T_3 is considered to multiply inherit.

   package P is
      type I is interface;
      procedure P (X : I) is abstract;
      type T1 is tagged private;
      procedure P (X : T1);
      type T2 is new I with private;
      procedure P (X : T2);
      type T3 is new T1 and I with private;
      procedure P (X : T3) is null;
   private
      pragma SPARK_Mode (Off);
      type T1 is tagged null record;
      procedure P (X : T1) is null;
      type T2 is new T1 and I with null record;
      procedure P (X : T2) is null;
      type T3 is new T2 with null record;
   end P;
begin
   null;
end Main;
