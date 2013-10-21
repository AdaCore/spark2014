--  Tests for definite types (discriminated/variant records with a
--  default discriminant).

package body Definite
is

   type Status is (Is_True, Is_False, File_Not_Found);
   --  A classic example of three valued logic.

   type T (D : Status := File_Not_Found) is record
      A : Natural;
      case D is
         when Is_True =>
            B : Natural;
         when Is_False =>
            X : Boolean;
         when File_Not_Found =>
            null;
      end case;
   end record;

   G : T;

   procedure Test_01 (X : out T;
                      Y : out Status)
   with Global  => (Output => G),
        Depends => (X => null,
                    Y => X,
                    G => null)
   is
   begin
      Y := X.D;
      X := (File_Not_Found, 0);
      G := (File_Not_Found, 0);
   end Test_01;

   procedure Test_01_Call (X : out T;
                           Y : out Status)
   with Global  => (Output => G),
        Depends => (X => null,
                    Y => X,
                    G => null)
   is
   begin
      Test_01 (X, Y);
   end Test_01_Call;

   procedure Test_01_B (Y : out Status)
   with Global  => (Output => G),
        Depends => (Y => G,
                    G => null)
   is
   begin
      Y := G.D;
      G := (File_Not_Found, 0);
   end Test_01_B;

   procedure Test_01_C (X : out T)
   with Global  => null,
        Depends => (X => X)
   is
   begin
      case X.D is
         when Is_True =>
            X := (Is_True, 0, 0);
         when Is_False =>
            X := (Is_False, 0, False);
         when others =>
            X := (File_Not_Found, 0);
      end case;
   end Test_01_C;

   procedure Test_01_D
   with Global  => (Output => G),
        Depends => (G => G)
   is
   begin
      case G.D is
         when Is_True =>
            G := (Is_True, 0, 0);
         when Is_False =>
            G := (Is_False, 0, False);
         when others =>
            G := (File_Not_Found, 0);
      end case;
   end Test_01_D;


   procedure Test_01_ND (X : out T;
                         Y : out Status)
   with Global => (Output => G)
   is
   begin
      Y := X.D;
      X := (File_Not_Found, 0);
      G := (File_Not_Found, 0);
   end Test_01_ND;

   procedure Test_01_ND_Use (X : out T;
                             Y : out Status)
   with Global => (Output => G)
   is
   begin
      Test_01_ND (X, Y);
   end Test_01_ND_Use;

   procedure Test_02 (X : out T;
                      Y : out Status)
   with Global  => null,
        Depends => (X => X,
                    Y => X)
   is
   begin
      Y := X.D;
      case Y is
         when Is_True =>
            X := (Is_True, 0, 0);
         when Is_False =>
            X := (Is_False, 0, False);
         when others =>
            X := (File_Not_Found, 0);
      end case;
   end Test_02;

   procedure Test_02_ND (X : out T;
                         Y : out Status)
   with Global => null
   is
   begin
      Y := X.D;
      case Y is
         when Is_True =>
            X := (Is_True, 0, 0);
         when Is_False =>
            X := (Is_False, 0, False);
         when others =>
            X := (File_Not_Found, 0);
      end case;
   end Test_02_ND;

   procedure Test_03 (X : out T)
   with Global  => null,
        Depends => (X => null,
                    null => X)
   is
   begin
      X := (File_Not_Found, 0);
   end Test_03;

   procedure Test_03_ND (X : out T)
   with Global => null
   is
   begin
      X := (File_Not_Found, 0);
   end Test_03_ND;

   procedure Test_04 (X : in out T;
                      I : in     Integer)
   with Global => null,
        Depends => (X => I,
                    null => X)
   is
   begin
      X := (File_Not_Found, I);
   end Test_04;

   procedure Test_05 (X :    out T;
                      I : in     Integer)
   with Global => null,
   Depends => (X => I,
               null => X)
   is
   begin
      X := (File_Not_Found, I);
   end Test_05;

end Definite;
