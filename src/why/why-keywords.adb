------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                     G N A T 2 W H Y - K E Y W O R D S                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2019-2023, AdaCore                     --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with String_Utils; use String_Utils;

package body Why.Keywords is
   --  This file is automatically generated by scripts/why3keywods.py

   procedure Update_Keywords (Keywords : out String_Utils.String_Sets.Set) is
   begin
      --  This part is automatically generated
      Keywords.Insert ("abstract");
      Keywords.Insert ("absurd");
      Keywords.Insert ("alias");
      Keywords.Insert ("any");
      Keywords.Insert ("as");
      Keywords.Insert ("assert");
      Keywords.Insert ("assume");
      Keywords.Insert ("at");
      Keywords.Insert ("axiom");
      Keywords.Insert ("begin");
      Keywords.Insert ("break");
      Keywords.Insert ("by");
      Keywords.Insert ("check");
      Keywords.Insert ("clone");
      Keywords.Insert ("coinductive");
      Keywords.Insert ("constant");
      Keywords.Insert ("continue");
      Keywords.Insert ("diverges");
      Keywords.Insert ("do");
      Keywords.Insert ("done");
      Keywords.Insert ("downto");
      Keywords.Insert ("else");
      Keywords.Insert ("end");
      Keywords.Insert ("ensures");
      Keywords.Insert ("epsilon");
      Keywords.Insert ("exception");
      Keywords.Insert ("exists");
      Keywords.Insert ("export");
      Keywords.Insert ("false");
      Keywords.Insert ("for");
      Keywords.Insert ("forall");
      Keywords.Insert ("fun");
      Keywords.Insert ("function");
      Keywords.Insert ("ghost");
      Keywords.Insert ("goal");
      Keywords.Insert ("if");
      Keywords.Insert ("import");
      Keywords.Insert ("in");
      Keywords.Insert ("inductive");
      Keywords.Insert ("invariant");
      Keywords.Insert ("label");
      Keywords.Insert ("lemma");
      Keywords.Insert ("let");
      Keywords.Insert ("match");
      Keywords.Insert ("meta");
      Keywords.Insert ("module");
      Keywords.Insert ("mutable");
      Keywords.Insert ("not");
      Keywords.Insert ("old");
      Keywords.Insert ("partial");
      Keywords.Insert ("predicate");
      Keywords.Insert ("private");
      Keywords.Insert ("pure");
      Keywords.Insert ("raise");
      Keywords.Insert ("raises");
      Keywords.Insert ("reads");
      Keywords.Insert ("rec");
      Keywords.Insert ("requires");
      Keywords.Insert ("return");
      Keywords.Insert ("returns");
      Keywords.Insert ("scope");
      Keywords.Insert ("so");
      Keywords.Insert ("then");
      Keywords.Insert ("theory");
      Keywords.Insert ("to");
      Keywords.Insert ("true");
      Keywords.Insert ("try");
      Keywords.Insert ("type");
      Keywords.Insert ("use");
      Keywords.Insert ("val");
      Keywords.Insert ("variant");
      Keywords.Insert ("while");
      Keywords.Insert ("with");
      Keywords.Insert ("writes");
      Keywords.Insert ("float");
      Keywords.Insert ("range");
      Keywords.Insert ("ref");

   end Update_Keywords;

end Why.Keywords;
