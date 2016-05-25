package Untangle is

   subtype Idx_T is Natural range 1 .. 100;

   type Point_T is
      record
         X, Y : Natural;
      end record;

   type Seq_T is array (Idx_T) of Point_T;

   type Exp_Seq_T is
      record
         Len    : Natural;
         Points : Seq_T;
      end record;

   type Opt_P_T is
      record
         Flag  : Boolean;
         Idx   : Idx_T;
         The_P : Point_T;
      end record;

   procedure Proc (R : in Exp_Seq_T; I: in Idx_T; Nf: out Opt_P_T);

end Untangle;
