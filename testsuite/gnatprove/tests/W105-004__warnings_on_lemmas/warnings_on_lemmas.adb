procedure Warnings_On_Lemmas with SPARK_Mode is
   V : Integer := 0;
   function Read_V return Integer is (V);
   function Cst return Integer is (0);
   Cst_A : not null access function return Integer := Cst'Access;
   type Named_F is not null access function return Integer;

   function Call_2 (B : Boolean; F, G : not null access function return Integer) return Integer is
      (if B then F.all else G.all)
   with Post => Call_2'Result = (if B then F.all else G.all),
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Higher_Order_Specialization);

   --  These lemmas can be specialized, no warnings
   procedure Lemma_Ok (B : Boolean; F, G : not null access function return Integer) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Ghost,
     Pre => B,
     Post => Call_2 (B, F, G) = F.all;

   procedure Lemma_Ok_2 (B : Boolean; F, G : not null access function return Integer) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Ghost,
     Pre => not B,
     Post => Call_2 (B, G, F) = F.all;

   procedure Lemma_Ok_3 (B : Boolean; F, G : not null access function return Integer) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Ghost,
     Contract_Cases =>
       (B      => Call_2 (B, F, G) = F.all,
        others => Call_2 (B, F, G) = G.all);

   --  This lemma has no Higher_Order_Specialization annotation, we have a warning
   procedure Lemma_No_Spec (B : Boolean; F, G : not null access function return Integer) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Ghost,
     Pre => B,
     Post => Call_2 (B, F, G) = F.all;

   --  These lemmas have no specializable calls to Call_2, we have warnings
   procedure Lemma_No_Call (B : not null access function return Boolean) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Ghost,
     Post => Call_2 (B.all, Read_V'Access, Read_V'Access) = V;

   procedure Lemma_No_Call_2 (B : not null access function return Boolean) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Ghost,
     Post => Call_2 (B.all, Cst_A, Cst_A) = Cst_A.all;

   procedure Lemma_No_Call_3 (B : not null access function return Boolean; F, G : Named_F) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Ghost,
     Pre => B.all,
     Post => Call_2 (B.all, F, G) = F.all;

   --  These lemmas have partially specializable calls to Call_2, we have warnings
   procedure Lemma_Partial_Call (B : Boolean; F : not null access function return Integer) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Ghost,
     Pre => B,
     Post => Call_2 (B, Read_V'Access, F) = V;

   procedure Lemma_Partial_Call_2 (B : Boolean; F : not null access function return Integer) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Ghost,
     Pre => B,
     Post => Call_2 (B, Cst_A, F) = Cst_A.all;

   procedure Lemma_Partial_Call_3 (B : Boolean; F : not null access function return Integer; G : Named_F) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Ghost,
     Pre => B,
     Post => Call_2 (B, F, G) = F.all;

   --  These lemmas contain two different specializable calls to Call_2, we have warnings
   procedure Lemma_Two_Calls (B : Boolean; F, G : not null access function return Integer) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Ghost,
     Post => Call_2 (B, F, G) = Call_2 (not B, G, F);

   procedure Lemma_Two_Calls_2 (B : Boolean; F, G, H : not null access function return Integer) with
     Annotate => (GNATprove, Always_Return),
     Annotate => (GNATprove, Automatic_Instantiation),
     Annotate => (GNATprove, Higher_Order_Specialization),
     Ghost,
     Pre => B,
     Post => Call_2 (B, F, G) = Call_2 (B, F, H);

   procedure Lemma_Ok (B : Boolean; F, G : not null access function return Integer) is null;
   procedure Lemma_Ok_2 (B : Boolean; F, G : not null access function return Integer) is null;
   procedure Lemma_Ok_3 (B : Boolean; F, G : not null access function return Integer) is null;
   procedure Lemma_No_Spec (B : Boolean; F, G : not null access function return Integer) is null;
   procedure Lemma_No_Call (B : not null access function return Boolean) is null;
   procedure Lemma_No_Call_2 (B : not null access function return Boolean) is null;
   procedure Lemma_No_Call_3 (B : not null access function return Boolean; F, G : Named_F) is null;
   procedure Lemma_Partial_Call (B : Boolean; F : not null access function return Integer) is null;
   procedure Lemma_Partial_Call_2 (B : Boolean; F : not null access function return Integer) is null;
   procedure Lemma_Partial_Call_3 (B : Boolean; F : not null access function return Integer; G : Named_F) is null;
   procedure Lemma_Two_Calls (B : Boolean; F, G : not null access function return Integer) is null;
   procedure Lemma_Two_Calls_2 (B : Boolean; F, G, H : not null access function return Integer) is null;
begin
   null;
end Warnings_On_Lemmas;
