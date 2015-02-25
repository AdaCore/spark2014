package body User is
   procedure User_Of_No_Contracts (X : out Integer) is
   begin
      No_Contracts (X);
   end User_Of_No_Contracts;

   procedure User_Of_G (X, Y : in out Integer) is
   begin
      G (X, Y);
   end User_Of_G;

   procedure User_Of_Dep (X : Integer; Y : out Integer) is
   begin
      Dep (X, Y);
   end User_Of_Dep;

   procedure User_Of_G_D (X : out Integer) is
   begin
      G_D (X);
   end User_Of_G_D;

   procedure User_Of_RG is
   begin
      RG;
   end User_Of_RG;

   procedure User_Of_RG_D is
   begin
      RG_D;
   end User_Of_RG_D;

   procedure User_Of_RD is
   begin
      RD;
   end User_Of_RD;

   procedure User_Of_G_RD is
   begin
      G_RD;
   end User_Of_G_RD;

   procedure User_Of_RG_RD is
   begin
      RG_RD;
   end User_Of_RG_RD;
end User;
