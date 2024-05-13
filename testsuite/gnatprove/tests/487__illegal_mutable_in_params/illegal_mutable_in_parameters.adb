procedure Illegal_Mutable_In_Parameters with SPARK_Mode is
   package Priv is
      type T is private;
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
   end Priv;

   package Vis is
      type T is private;
   private
      type T is access Integer;
   end Vis;

   procedure Ok_Update (X : Priv.T; Y : Vis.T) with
     Import;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, Priv.T);
   pragma Annotate  (GNATprove, Mutable_In_Parameters, Vis.T);

   --  Bad number of parameters

   procedure Bad_Update_1 (X : Priv.T) with
     Import;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, "foo", Priv.T);

   --  Third parameter shall be an entity

   procedure Bad_Update_2 with
     Import;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, "foo");

   --  Third parameter shall be in SPARK

   package Bad with SPARK_Mode => Off is
      type T is private;
   private
      type T is access Integer;
   end Bad;

   procedure Bad_Update_3 (X : Bad.T) with
     Import;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, Bad.T);

   --  Third parameter shall be a private type

   package Bad_Vis is
      type T is access Integer;
   end Bad_Vis;

   procedure Bad_Update_4 (X : Bad_Vis.T) with
     Import;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, Bad_Vis.T);

   --  Third parameter shall not be tagged

   package Bad_Tag is
      type T is tagged private;
   private
      pragma SPARK_Mode (Off);
      type T is tagged null record;
   end Bad_Tag;

   procedure Bad_Update_5 (X : Bad_Tag.T) with
     Import;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, Bad_Tag.T);

   --  Third parameter shall not have discriminants

   package Bad_Discr is
      type T (B : Boolean) is private;
   private
      pragma SPARK_Mode (Off);
      type T (B : Boolean) is null record;
   end Bad_Discr;

   procedure Bad_Update_6 (X : Bad_Discr.T) with
     Import;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, Bad_Discr.T);

   --  Third parameter shall ultimately be private or an access-to-variable type

   package Bad_Full_View is
      type T is private;
   private
      type T is null record;
   end Bad_Full_View;

   procedure Bad_Update_6 (X : Bad_Full_View.T) with
     Import;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, Bad_Full_View.T);

   --  Pragma should be located after a subprogram

   Bad_Update_7 : Priv.T;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, Priv.T);

   package Bad_Update_8 is
      procedure P (X : Priv.T) is null;
   end Bad_Update_8;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, Priv.T);

   --  Pragma should be located after a subprogram with side effects

   function Bad_Update_9 (X : Priv.T) return Boolean with
     Import;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, Priv.T);

   function Ok_Update_9 (X : Priv.T) return Boolean with
     Side_Effects,
     Import;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, Priv.T);

   --  Pragma should not be located after a dispatching subprogram

   package Bad_Dispatch is
      type T is tagged null record;

      procedure Bad_Update_10 (X : Priv.T; Y : T) with
        Import;
      pragma Annotate  (GNATprove, Mutable_In_Parameters, Priv.T);
   end Bad_Dispatch;

   --  Pragma should not be located after an automatically instantiated lemma

   function F return Boolean is (True);

   procedure Bad_Update_11 (X : Priv.T) with
     Ghost,
     Annotate => (GNATprove, Automatic_Instantiation),
     Import;
   pragma Annotate  (GNATprove, Mutable_In_Parameters, Priv.T);

   procedure Bad_Update_12 (X : Priv.T) with
     Ghost,
     Import;
   pragma Annotate (GNATprove, Mutable_In_Parameters, Priv.T);
   pragma Annotate (GNATprove, Automatic_Instantiation, Bad_Update_12);

   --  There should be at least an applicable IN parameter

   procedure Bad_Update_13 (X : Priv.T) with
     Import;
   pragma Annotate (GNATprove, Mutable_In_Parameters, Vis.T);
begin
   null;
end Illegal_Mutable_In_Parameters;
