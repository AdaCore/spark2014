package TAA
  with SPARK_Mode => On
is
   -- TU: 1. All forms of access type and parameter declarations are
   --  prohibited. [This follows from the rule forbidding use of the
   --  Ada reserved word **access**.]

   -- TU: 2. The attribute 'Access shall not be denoted.

   type T is access all Integer;

   X : aliased Integer;

   Y : T := X'Access;

   procedure Op (X : access Integer);


end TAA;
