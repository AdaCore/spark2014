package body Excep
  with SPARK_Mode => On
is
   -- TU: 1. Exception handlers are not permitted in |SPARK|.

   procedure Bad1 (X : in out Integer) is
   begin
      X := X + 1;
   exception -- illegal - RM 11.2(1)
      when Constraint_Error =>
         null;
   end Bad1;

   procedure Bad2 (X : in out Integer) is
   begin
      if X = Integer'Last then
         X := X - 1;
         raise Constraint_Error; -- illegal - RM 11.3(1)
      end if;
      X := X + 1;
   end Bad2;

   procedure Bad3 (X : in out Integer) is
   begin
      X := X + 1;
      raise Constraint_Error; -- illegal - RM 11.3(1)
      X := X + 2;
   end Bad3;

   procedure Bad4 (X : in out Integer) is
   begin
      X := X + 1;
      raise Constraint_Error with "Hello"; -- illegal - RM 11.3(2)
   end Bad4;

   procedure OK1 (X : in out Integer) is
   begin
      if X = Integer'Last then
         raise Constraint_Error; -- OK - RM 11.3(1)
      end if;
      X := X + 1;
   end OK1;

   procedure OK2 (X : in out Integer) is
   begin
      X := X + 1;
      raise Constraint_Error; -- OK - RM 11.3(1)
   end OK2;

end Excep;
