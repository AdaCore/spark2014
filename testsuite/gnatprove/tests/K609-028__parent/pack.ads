with Ext_Pack; pragma Elaborate_All (Ext_Pack);

package Pack with
  Initializes    => (N => Ext_Pack.C)
is

   N : Integer := Ext_Pack.C;

end Pack;
