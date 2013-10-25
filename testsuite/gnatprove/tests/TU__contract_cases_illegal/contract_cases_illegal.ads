package Contract_Cases_Illegal
  with SPARK_Mode
is
   function Positive (X : Integer) return Boolean;

   function Negative (X : Integer) return Boolean;

   procedure Proc (X : Integer ; Y : Integer ; Z : out Integer)
     --  TU: 1. A Contract_Cases aspect may have at most one **others**
     --  ``contract_case`` and if it exists it must be the last one in the
     --  ``contract_case_list``.
     with Pre            => (X in -1_000 .. 1_000 and Y in -1_000 .. 1_000),
          Post           => Z = X * Y,
          Contract_Cases => (others => Z <= 0,
                             Positive (X) and Positive (Y) => Positive (Z),
                             Negative (X) and Negative (Y) => Positive (Z));


   procedure Proc2 (X : in out Integer)
     --  TU: 2. A ``consequence`` expression is considered to be a
     --  postcondition expression for purposes of determining the legality of
     --  Old or Result ``attribute_references``. An expression occurring
     --  within an ``consequence`` expression is defined to be not potentially
     --  unevaluated. [This means that Ada's rule that "The prefix of an Old
     --  attribute_reference that is potentially unevaluated shall statically
     --  denote an entity" is ineffective anywhere within a ``consequence``
     --  expression.]
     with Contract_Cases => (Positive (X'Old) => X = X'Old * X'Old,
                             Negative (X)'Old => X = - (X'Old * X'Old),
                             others           => X = 0);


   function Func (X, Y : Integer) return Integer
     --  TU: 2. A ``consequence`` expression is considered to be a
     --  postcondition expression for purposes of determining the legality of
     --  Old or Result ``attribute_references``. An expression occurring
     --  within an ``consequence`` expression is defined to be not potentially
     --  unevaluated. [This means that Ada's rule that "The prefix of an Old
     --  attribute_reference that is potentially unevaluated shall statically
     --  denote an entity" is ineffective anywhere within a ``consequence``
     --  expression.]
     with Contract_Cases => (Positive(Func'Result) => X * Y > 0);
end Contract_Cases_Illegal;
