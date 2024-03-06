procedure Test with SPARK_Mode is

   type R (D : Integer := 1) is record
      A, B : Integer;
   end record;

   procedure P (X : out R; B : out Boolean) with
     Depends => (B => X, X => null);

   procedure P (X : out R; B : out Boolean) is
   begin
      B := X.D = 0;
      X := (D => 12, others => 0);
   end P;

   type RR is record
      F : R;
   end record;

   procedure Q_1 (X : out RR; B : out Boolean) with
     Depends => (B => null, X => null);

   procedure Q_1 (X : out RR; B : out Boolean) is
   begin
      P (X.F, B); --  @INITIALIZED:CHECK
   end Q_1;

   type A is array (Integer range 1 .. 1) of R;

   procedure Q_2 (X : out A; B : out Boolean) with
     Depends => (B => null, X => null);

   procedure Q_2 (X : out A; B : out Boolean) is
   begin
      for I in A'Range loop
         P (X (I), B); --  @INITIALIZED:CHECK
      end loop;
   end Q_2;

begin
   null;
end Test;
