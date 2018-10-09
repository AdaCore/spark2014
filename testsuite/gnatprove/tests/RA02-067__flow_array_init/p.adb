--
-- \brief  JWX binding to libsparkcrypto
-- \author Alexander Senier
-- \date   2018-06-06
--
-- Copyright (C) 2018 Componolit GmbH
--
-- This file is part of JWX, which is distributed under the terms of the
-- GNU Affero General Public License version 3.
--

package body P is

   procedure Proc (Output : out UA)
   is
      Value : CA;
   begin
      Output := (others => 0);
      for O in Output'Range
      loop
         Value := (others => 0);
         for J in Value'Range
         loop
            Value (J) := 0;
            Output (O) := 0;
         end loop;
      end loop;
   end Proc;

end P;
