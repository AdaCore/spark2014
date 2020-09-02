package body Foo with SPARK_Mode is

   procedure Recursive_Proc_W_Variant (X : Natural) is
   begin
      if X > 0 then
         Recursive_Proc_W_Variant (X - 1);
      end if;
   end Recursive_Proc_W_Variant;

   procedure Recursive_Proc_W_Variant_Terminating (X : Natural)
   with
     Subprogram_Variant => (Decreases => X),
     Annotate           => (GNATprove, Terminating)
   is
   begin
      if X > 0 then
         Recursive_Proc_W_Variant_Terminating (X - 1);
      end if;
   end Recursive_Proc_W_Variant_Terminating;

   procedure Call_To_Recursive_W_Variant_A with Annotate => (GNATprove, Terminating) is
   begin
      Recursive_Proc_W_Variant (3);
   end Call_To_Recursive_W_Variant_A;

   procedure Call_To_Recursive_W_Variant_B with Annotate => (GNATprove, Terminating) is
   begin
      Recursive_Proc_W_Variant (3);
      while True loop
         null;
      end loop;
   end Call_To_Recursive_W_Variant_B;

   procedure Mutually_A (X : Natural) with
     Global             => null,
     Annotate           => (GNATprove, Terminating),
     Subprogram_Variant => (Decreases => X);

   procedure Mutually_B (X : Natural) with
     Global             => null,
     Subprogram_Variant => (Decreases => X);

   procedure Mutually_A (X : Natural) is
   begin
      if X > 0 then
         Mutually_B (X - 1);
      end if;
   end Mutually_A;

   procedure Mutually_B (X : Natural) is
   begin
      if X > 0 then
         Mutually_A (X - 1);
      end if;
   end Mutually_B;

   procedure Mutually_C (X : Natural) with
     Global             => null,
     Subprogram_Variant => (Decreases => X);

   procedure Mutually_D (X : Natural) with
     Global             => null,
     Annotate           => (GNATprove, Terminating);

   procedure Mutually_C (X : Natural) is
   begin
      if X > 0 then
         Mutually_D (X - 1);
      end if;
   end Mutually_C;

   procedure Mutually_D (X : Natural) is
   begin
      if X > 0 then
         Mutually_C (X - 1);
      end if;
   end Mutually_D;

   procedure Mutually_E (X : Natural) with
     Global             => null;

   procedure Mutually_F (X : Natural) with
     Global             => null,
     Annotate           => (GNATprove, Terminating),
     Subprogram_Variant => (Decreases => X);

   procedure Mutually_E (X : Natural) is
   begin
      if X > 0 then
         Mutually_F (X - 1);
      end if;
   end Mutually_E;

   procedure Mutually_F (X : Natural) is
   begin
      if X > 0 then
         Mutually_E (X - 1);
      end if;
   end Mutually_F;

   procedure Mutually_G (X : Natural) with
     Global             => null;

   procedure Mutually_H (X : Natural) with
     Global             => null,
     Annotate           => (GNATprove, Terminating),
     Subprogram_Variant => (Decreases => X);

   procedure Mutually_G (X : Natural) is
   begin
      if X > 0 then
         Mutually_H (X - 1);
      end if;
      while True loop
         null;
      end loop;
   end Mutually_G;

   procedure Mutually_H (X : Natural) is
   begin
      if X > 0 then
         Mutually_G (X - 1);
      end if;
   end Mutually_H;

   procedure Mutually_I (X : Natural) with
     Subprogram_Variant => (Decreases => X),
     Global             => null;

   procedure Mutually_J (X : Natural) with
     Global             => null,
     Annotate           => (GNATprove, Terminating),
     Subprogram_Variant => (Decreases => X);

   procedure Mutually_I (X : Natural) is
   begin
      if X > 0 then
         Mutually_J (X - 1);
      end if;
      while True loop
         null;
      end loop;
   end Mutually_I;

   procedure Mutually_J (X : Natural) is
   begin
      if X > 0 then
         Mutually_I (X - 1);
      end if;
   end Mutually_J;

   procedure Invisible_Call_To_Nonterminating with Annotate => (GNATprove, Terminating) is
      procedure A with Global => null;
      procedure B with Annotate => (GNATprove, Terminating), Global => null;
      procedure C with Global => null;

      procedure A is begin B; end A;
      procedure B is begin C; end B;
      procedure C is
      begin
         while True loop
            null;
         end loop;
      end C;

   begin
      A;
   end Invisible_Call_To_Nonterminating;

   function Subnested_Package (X : Natural) return Natural with
     Annotate           => (GNATprove, Terminating),
     Subprogram_Variant => (Decreases => X)
   is
      function Aux (I : Natural) return Natural with
        Subprogram_Variant => (Decreases => I) is
         package Nested is
            Foo : Natural := (if I = 0 then 0 else Subnested_Package (I - 1));
         end Nested;
      begin
         return Nested.Foo;
      end Aux;
   begin
      if X = 0 then
         return 0;
      else
         return Aux (X - 1);
      end if;
   end Subnested_Package;

   function Subnested_Package_Wo_Variant (X : Natural) return Natural with
     Annotate           => (GNATprove, Terminating),
     Subprogram_Variant => (Decreases => X)
   is
      function Aux (I : Natural) return Natural is
         package Nested is
            Foo : Natural := (if I = 0 then 0 else Subnested_Package_Wo_Variant (I - 1));
         end Nested;
      begin
         return Nested.Foo;
      end Aux;
   begin
      if X = 0 then
         return 0;
      else
         return Aux (X - 1);
      end if;
   end Subnested_Package_Wo_Variant;

   function Function_W_Nested_Package (X : Natural) return Natural with
     Annotate           => (GNATprove, Terminating),
     Subprogram_Variant => (Decreases => X)
   is
      package Nested is
         Foo : Natural := (if X = 0 then 0 else Function_W_Nested_Package (X - 1));
      end Nested;
   begin
      return Nested.Foo;
   end Function_W_Nested_Package;

end Foo;
