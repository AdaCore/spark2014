-- The 1553 bus interface for Remote Terminals (RT)
--
-- $Id: rt1553.ads,v 1.1.1.1 2004/01/12 19:29:12 adi Exp $
--
-- $Log: rt1553.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.6  2003/08/17 22:04:48  adi
-- Added lru_number lookup
--
-- Revision 1.5  2003/08/17 15:06:04  adi
-- Added is_fresh, is_valid
--
-- Revision 1.4  2003/02/12 21:25:03  adi
-- Added Set_Message_Valid
--
-- Revision 1.3  2003/02/05 22:50:45  adi
-- Updated for renamed type
--
-- Revision 1.2  2003/02/03 23:19:28  adi
-- Added Acknowledge_Message
--
-- Revision 1.1  2003/02/03 18:35:24  adi
-- Initial revision
--
--
--
with Bus;
with SystemTypes;
--# inherit SystemTypes,Bus;
package RT1553
is
   -- Symbolic names for the Lrus
   type Lru_Name is
     (Barometer,
      Asi,
      Ins,
      Compass,
      Fuel,
      Fuze,
      Radar,
      Infrared,
      Fins,
      Motor,
      Destruct,
      Warhead
      );

   function Lru_Number(L : Lru_Name) return Bus.Lru_Index;

   -- Write out data to the BC
   procedure Set_Message_Valid(Subaddress_Idx : in Bus.Lru_Subaddress_Index;
                               Src     : in Lru_Name);
   --# global in out Bus.Inputs;
   --# derives Bus.Inputs from *, Subaddress_Idx, Src;

   procedure Write_Word(Data    : in Bus.Word;
                        Idx     : in Bus.Word_Index;
                        Subaddress_Idx : in Bus.Lru_Subaddress_Index;
                        Src     : in Lru_Name);
   --# global in out Bus.Inputs;
   --# derives Bus.Inputs from *, Data, Idx, Subaddress_Idx, Src;

   procedure Write_Message(Data    : in Bus.Message;
                           Subaddress_Idx : in Bus.Lru_Subaddress_Index;
                           Src     : in Lru_Name);
   --# global in out Bus.Inputs;
   --# derives Bus.Inputs from *, Data, Subaddress_Idx, Src;


   -- Read data sent to the RT

   procedure Read_Word(Src     : in  Lru_Name;
                       Idx     : in  Bus.Word_Index;
                       Subaddress_Idx : in  Bus.Lru_Subaddress_Index;
                       Data    : out Bus.Word);
   --# global in Bus.Outputs;
   --# derives Data from Src, Idx, Subaddress_Idx, Bus.Outputs;

   procedure Read_Message(Src     : in  Lru_Name;
                          Subaddress_Idx : in  Bus.Lru_Subaddress_Index;
                          Data    : out Bus.Message);
   --# global in Bus.Outputs;
   --# derives Data from Src, Subaddress_Idx, Bus.Outputs;

   procedure Acknowledge_Message(Src     : in  Lru_Name;
                                 Subaddress_Idx : in  Bus.Lru_Subaddress_Index);
   --# global in out Bus.Outputs;
   --# derives Bus.Outputs from *, Src, Subaddress_Idx;

     -- See if a message is fresh
   function Is_Fresh(Src : Lru_Name;
                     Subaddress_Idx : Bus.Lru_Subaddress_Index)
                    return Boolean;
   --# global in Bus.Outputs;

   -- See if a message is valid
   function Is_Valid(Src : Lru_Name;
                     Subaddress_Idx : Bus.Lru_Subaddress_Index)
                    return Boolean;
   --# global in Bus.Outputs;

end RT1553;

