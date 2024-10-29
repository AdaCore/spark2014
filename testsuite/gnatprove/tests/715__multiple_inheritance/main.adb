procedure Main with SPARK_Mode is

   --  Subprogram implicitly inherited from parent and interface

   package A is
      type T is tagged null record;
      procedure P (X : T) is null;
      type I is interface;
      procedure P (X : I) is abstract;
      type U is new T and I with null record;
   end A;

   --  Subprogram implicitly inherited from several of the extra interface

   package B is
      type T is tagged null record;
      type I is interface;
      procedure P (X : I) is null;
      type J is interface;
      procedure P (X : J) is null;
      type U is new T and I and J with null record;
   end B;

   --  Subprogram implicitly inherited from parent and interface, with parent
   --  itself an interface.

   package C is
      type T is interface;
      procedure P (X : T) is null;
      type I is interface;
      procedure P (X : I) is abstract;
      package Inner is
         type U is new T and I with null record;
      end Inner;
   end C;

   --  Subprogram explicitly overridden for parent and interface

   package D is
      type T is tagged null record;
      procedure P (X : T) is null;
      type I is interface;
      procedure P (X : I) is abstract;
      type U is new T and I with null record;
      procedure P (X : U) is null;
   end D;

   --  Subprogram explicitly overridden for multiple extra interfaces

   package E is
      type T is tagged null record;
      type I is interface;
      procedure P (X : I) is null;
      type J is interface;
      procedure P (X : J) is null;
      type U is new T and I and J with null record;
      procedure P (X : U) is null;
   end E;

   --  Subprogram explicitly overridden, from parent and interface, parent
   --  itself an interface.

   package F is
      type T is interface;
      procedure P (X : T) is null;
      type I is interface;
      procedure P (X : I) is abstract;
      type U is new T and I with null record;
      procedure P (X : U) is null;
   end F;

   --  Subprogram implicitly inherited across a fairly long/complex chain
   --  before the joining interface.

   package G is
      package Inner is
         type T is tagged null record;
         procedure P (X : T) is null;
         type U is new T with private;
      private
         type V is new T with null record;
         procedure P (X : V) is null;
         package InnerMore is
            type W is new V with private;
         private
            type WW is new V with null record;
            type W is new WW with null record;
         end InnerMore;
         type U is new InnerMore.W with null record;
      end Inner;
      type I is interface;
      procedure P (X : I) is abstract;
      type Bad is new Inner.U and I with null record;
   end G;

   --  Mixed SPARK_Mode for roots when implicitly inheriting

   package H is
      type T is tagged null record;
      procedure P (X : T) is null with SPARK_Mode => Off;
      type I is interface;
      procedure P (X : I) is abstract;
      type U is new T and I with null record;
   end H;

   package I is
      type T is tagged null record;
      procedure P (X : T) is null;
      type I is interface;
      procedure P (X : I) is null with SPARK_Mode => Off;
      type U is new T and I with null record;
   end I;

   package J is
      type T is tagged null record;
      type I is interface;
      procedure P (X : I) is null;
      type J is interface;
      procedure P (X : J) is null with SPARK_Mode => Off;
      type V is new T and I and J with null record;
   end J;

   --  Multiply inherited subprogram is fine if SPARK_Mode is Off

   package K is
      type T is tagged null record;
      procedure P (X : T) is null with SPARK_Mode => Off;
      type I is interface;
      procedure P (X : I) is null with SPARK_Mode => Off;
      type U is new T and I with null record;
   end K;

   package L is
      type T is tagged null record;
      procedure P (X : T) is null;
      type I is interface;
      procedure P (X : I) is null;
      type J is interface;
      procedure P (X : J) is null with SPARK_Mode => Off;
      type K is interface;
      procedure P (X : K) is null with SPARK_Mode => Off;
      type U is new T and I and J and K with null record;
      procedure P (X : U) is null with SPARK_Mode => Off;
   end L;

   --  Redundant interfaces are ignored.

   package M is
     type I is interface;
     procedure P (X : I) is null;
     type T is new I with null record;
     procedure P (X : T) is null;
     type U is new T and I with null record;
     procedure P (X : U) is null;
     type V is new U with null record;
     procedure P (X : V) is null;
   end M;


   --  Multiple inheritance outside of SPARK is fine

   package Hidden_Multiple_Inheritance is
      type T is tagged null record;
      type I is interface;
      procedure P (X : I) is null;
      type U is new T and I with null record;
      procedure P (X : U) is null with SPARK_Mode => Off;
      type J is interface;
      procedure P (X : J) is null with SPARK_Mode => Off;
      type V is new U and J with null record;
      procedure P (X : V) is null with SPARK_Mode => Off;
      type W is new T and I with null record;
      procedure P (X : W) is null;
   end Hidden_Multiple_Inheritance;

begin
   null;
end Main;
