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


package P is

   type UA is array (Integer range <>) of Integer;
   -- Unconstrained array

   type Index is range 0 .. 3;
   -- Index

   type CA is array (Index) of Integer;
   -- Constrained array

   procedure Proc (Output : out UA);

end P;
