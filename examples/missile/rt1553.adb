-- The 1553 bus interface for the Remote Terminal (RT)
--
-- $Id: rt1553.adb,v 1.1.1.1 2004/01/12 19:29:12 adi Exp $
--
-- $Log: rt1553.adb,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.6  2003/08/17 22:04:38  adi
-- Added lru_number
--
-- Revision 1.5  2003/08/17 15:06:13  adi
-- Added is_fresh, is_valid
--
-- Revision 1.4  2003/02/12 21:24:55  adi
-- Added Set_Message_Valid
--
-- Revision 1.3  2003/02/05 22:51:25  adi
-- Fixed for renamed file
--
-- Revision 1.2  2003/02/03 23:19:38  adi
-- Added Acknowledge_Message
--
-- Revision 1.1  2003/02/03 18:35:30  adi
-- Initial revision
--
--
--
package body RT1553
is
   -- Convert LRU names to LRU indices
   type Lru_Table is array(Lru_Name) of Bus.Lru_Index;
   Lru_Names : constant Lru_Table
     := Lru_Table'(Barometer => 1,
                   Asi      => 2,
                   Ins      => 3,
                   Compass  => 4,
                   Fuel     => 5,
                   Fuze     => 6,
                   Radar    => 7,
                   Infrared => 8,
                   Fins     => 9,
                   Motor    => 10,
                   Destruct => 11,
                   Warhead  => 12);

   function Lru_Number(L : Lru_Name) return Bus.Lru_Index
   is begin
      return Lru_Names(L);
   end Lru_Number;

   -- Write out data to the BC

   procedure Set_Message_Valid(Subaddress_Idx : in Bus.Lru_Subaddress_Index;
                               Src     : in Lru_Name)
   is
   begin
      Bus.Set_BC_Message_Valid(Src => Lru_Names(src),
                               Subaddress_Idx => Subaddress_Idx);
   end Set_Message_Valid;


   procedure Write_Word(Data    : in Bus.Word;
                        Idx     : in Bus.Word_Index;
                        Subaddress_Idx : in Bus.Lru_Subaddress_Index;
                        Src     : in Lru_Name)
   is
   begin
      Bus.Write_BC_Word(Src => Lru_Names(src),
                        Data => Data,
                        Idx => Idx,
                        Subaddress_Idx => Subaddress_Idx);
   end Write_Word;

   procedure Write_Message(Data    : in Bus.Message;
                           Subaddress_Idx : in Bus.Lru_Subaddress_Index;
                           Src     : in Lru_Name)
   is
   begin
      Bus.Write_BC_Message(Src => Lru_Names(src),
                           Data => Data,
                           Subaddress_Idx => Subaddress_Idx);
   end Write_Message;

   -- Read data sent to the RTs

   procedure Read_Word(Src     : in  Lru_Name;
                       Idx     : in  Bus.Word_Index;
                       Subaddress_Idx : in  Bus.Lru_Subaddress_Index;
                       Data    : out Bus.Word)
   is
   begin
      Bus.Read_RT_Word(Idx => Idx,
                       Subaddress_Idx => Subaddress_Idx,
                       Data => Data,
                       Dest => Lru_Names(Src));
   end Read_Word;

   procedure Read_Message(Src     : in  Lru_Name;
                          Subaddress_Idx : in  Bus.Lru_Subaddress_Index;
                          Data    : out Bus.Message)
   is
   begin
      Bus.Read_RT_Message(Subaddress_Idx => Subaddress_Idx,
                          Data => Data,
                          Dest => Lru_Names(Src));
   end Read_Message;

   procedure Acknowledge_Message(Src     : in  Lru_Name;
                              Subaddress_Idx : in  Bus.Lru_Subaddress_Index)
   is
   begin
      Bus.Acknowledge_RT_Message(Subaddress_Idx => Subaddress_Idx,
                                 Dest => Lru_Names(Src));
   end Acknowledge_Message;

       -- See if a message is fresh
   function Is_Fresh(Src : Lru_Name;
                     Subaddress_Idx : Bus.Lru_Subaddress_Index)
                    return Boolean
   is begin
      return Bus.Is_rt_Fresh(Lru_Names(Src),Subaddress_Idx);
   end Is_Fresh;

   -- See if a message is valid
   function Is_Valid(Src : Lru_Name;
                     Subaddress_Idx : Bus.Lru_Subaddress_Index)
                    return Boolean
   is begin
      return Bus.Is_rt_Valid(Lru_Names(Src),Subaddress_Idx);
   end Is_Valid;


end RT1553;

