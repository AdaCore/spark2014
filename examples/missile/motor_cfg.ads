-- Motor configuration
--
-- $Log: motor_cfg.ads,v $
-- Revision 1.1.1.1  2004/01/12 19:29:12  adi
-- Added from tarfile
--
--
-- Revision 1.3  2003/09/12 21:10:51  adi
-- Allowed power to be 0
--
-- Revision 1.2  2003/09/01 18:38:16  adi
-- Increased burn rate
--
-- Revision 1.1  2003/08/31 21:08:52  adi
-- Initial revision
--
--
with Measuretypes;
--# inherit measuretypes;
package Motor_Cfg
is
   -- Max and min power rating
   Max_Power : constant Measuretypes.Newton := 35_000;
   Min_power : constant Measuretypes.Newton := 0;

   -- Acceleration movement in delta-newtons/sec
   burn_Rate : constant := 5_000;

   subtype Motor_Power is Measuretypes.Newton
     range Min_Power .. Max_Power;

end motor_Cfg;

