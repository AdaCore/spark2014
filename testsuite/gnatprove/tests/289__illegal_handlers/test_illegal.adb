procedure Test_Illegal with SPARK_Mode is

   --  Wrong number of parameters

   type T1 is access procedure with
     Annotate => (GNATprove, Handler, "foo");

   --  Third parameter shall be an entity

   pragma Annotate (GNATprove, Handler, 12);

   --  Wrong placement

   type T2 is access procedure;
   X : T2;
   pragma Annotate (GNATprove, Handler, T2);

   --  Annotation can only be on an access-to-subprogram types

   procedure P with
     Annotate => (GNATprove, Handler);
   procedure P is null;
   type Int_Acc is access Integer with
     Annotate => (GNATprove, Handler);

   --  Handlers cannot have pre or postconditions

   type With_Pre is access procedure (X : Integer) with
     Pre => X < Integer'Last,
     Annotate => (GNATprove, Handler);

   type With_Post is access procedure (X : out Integer) with
     Post => X < Integer'Last,
     Annotate => (GNATprove, Handler);

   --  OK

   type T3 is access procedure with
     Annotate => (GNATprove, Handler);

   procedure Call_Handler_1 (X : not null T3) is
   begin
      X.all; --  Illegal, cannot call handler
   end Call_Handler_1;

   procedure Call_Handler_2 (X : not null T3) is
      Y : access procedure := X; --  Illegal, Handler annotation shall be preserved
   begin
      Y.all;
   end Call_Handler_2;

begin
   null;
end;
