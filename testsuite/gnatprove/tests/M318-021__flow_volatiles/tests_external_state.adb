package body Tests_External_State
  with SPARK_Mode,
       Refined_State => (State       => Vol,
                         State_AR    => Vol_AR,
                         State_AR_EW => Vol_AR_EW,
                         State_AW    => Vol_AW,
                         State_AW_ER => Vol_AW_ER)
is
   Vol : Integer
     with Volatile;

   Vol_AR : Integer := 0
     with Volatile,
          Async_Readers;

   Vol_AR_EW : Integer := 0
     with Volatile,
          Async_Readers,
          Effective_Writes;

   Vol_AW : Integer
     with Volatile,
          Async_Writers;

   Vol_AW_ER : Integer
     with Volatile,
          Async_Writers,
          Effective_Reads;

   --  Set/Get

   procedure Set (X : Integer)
     with Refined_Global  => (Output => Vol),
          Refined_Depends => (Vol => X)
   is
   begin
      Vol := X;
   end Set;

   procedure Get (X : out Integer)
     with Refined_Global  => (In_Out => Vol),
          Refined_Depends => ((X, Vol) => Vol)
   is
   begin
      X := Vol;
   end Get;

   -- Set_AR/Get_AR

   procedure Set_AR (X : Integer)
     with Refined_Global  => (Output => Vol_AR),
          Refined_Depends => (Vol_AR => X)
   is
   begin
      Vol_AR := X;
   end Set_AR;

   procedure Get_AR (X : out Integer)
     with Refined_Global  => Vol_AR,
          Refined_Depends => (X => Vol_AR)
   is
   begin
      X := Vol_AR;
   end Get_AR;

   -- Set_AR_EW/Get_AR_EW

   procedure Set_AR_EW (X : Integer)
     with Refined_Global  => (Output => Vol_AR_EW),
          Refined_Depends => (Vol_AR_EW => X)
   is
   begin
      Vol_AR_EW := X;
   end Set_AR_EW;

   procedure Get_AR_EW (X : out Integer)
     with Refined_Global  => Vol_AR_EW,
          Refined_Depends => (X => Vol_AR_EW)
   is
   begin
      X := Vol_AR_EW;
   end Get_AR_EW;

   -- Set_AW/Get_AW

   procedure Set_AW (X : Integer)
     with Refined_Global  => (Output => Vol_AW),
          Refined_Depends => (Vol_AW => X)
   is
   begin
      Vol_AW := X;
   end Set_AW;

   procedure Get_AW (X : out Integer)
     with Refined_Global  => Vol_AW,
          RefineD_Depends => (X => Vol_AW)
   is
   begin
      X := Vol_AW;
   end Get_AW;

   -- Set_AW_ER/Get_AW_ER

   procedure Set_AW_ER (X : Integer)
     with Refined_Global  => (Output => Vol_AW_ER),
          Refined_Depends => (Vol_AW_ER => X)
   is
   begin
      Vol_AW_ER := X;
   end Set_AW_ER;

   procedure Get_AW_ER (X : out Integer)
     with Refined_Global  => (In_Out => Vol_AW_ER),
          Refined_Depends => ((X, Vol_AW_ER) => Vol_AW_ER)
   is
   begin
      X := Vol_AW_ER;
   end Get_AW_ER;
end Tests_External_State;
