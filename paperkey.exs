############
# Copyright (c) 2015 Arnaud Wetzel : MIT License :
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
# THE SOFTWARE.
############

# GPG priv key backup, Elixir version of David Shaw Paperkey, totally compatible with it (mode import/export "hexa"):
#
# The goal of this implementation is to be able to understand the import algorithm more easily than with David Shaw impl
# to be less dependent on its implementation, and easily rewrite it in any modern (future ?) language if needed
# The whole import code is only 40 lines of code thanks to Erlang bin syntax, in Paperkey.put_paperkeys which uses:
# - Pgp.decode/encode (pgp_bin<=>[{rfc4880_tag,rfc4880_data}]), 
# - Pgp.fingerprint (rfc4880_data=>gpg_fingerprint), 
# - Paperkey.decode (paperkey_bin=>%{gpg_fingerprint=>rfc4880_privkey})
#
# My usage to backup keys:
# 
# Get a hexa (or base64 for big one) readable version with explanations
# > gpg --export-secret-key A81C573A | elixir paperkey.exs export hexa > paperkeys.txt
#
# Split base64 raw into Level 31 QR codes
# > gpg --export-secret-key A81C573A | elixir paperkey.exs export binary | openssl enc -base64 | split -b 1835 - key-
# > for K in key-*; do; cat $K | qrencode -S -v 31 -l L -o $K.png ; done
#
# print paperkeys.txt on recto 
# then key-*.png images on verso (2 Level 31 QR codes are OK per A4 page)
#  
# My usage to restore keys:
#
# get pgp public certificate to pub.pgp
# Use QR reader (even with my webcam for 2 4096 keys) to read printed QR, concat them and copy result to the clipboard
# > paste | elixir paperkey.exs import base64 pub.pgp priv.pgp
#
# if impossible to scan the QR code, then scan your page containing the hexadecimal, crop to take only the hexa part
# put a tesseract "paperkey_conf" config file containing (no state + hexa char only): 
#     tessedit_char_whitelist 0123456789ABCDEF:
#     load_bigram_dawg F
# > tesseract yourscan.png stdout -psm 6 paperkey_conf > ocrhexa
# > cat ocrhexa | elixir paperkey.exs import hexa export_pub_test.pgp priv_test.pgp
# Iteratively correct your ocr export using the crc24  validation
# priv.pgp contains now the private keys !

defmodule Pgp do
  import Bitwise
  def decode(bin), do: decode(bin,[])
  def decode(<<1::size(1),1::size(1),tag::size(6),rest::binary>>,acc) do
    {data,rest} = packet_new(rest); decode(rest,[%{tag: tag, data: IO.iodata_to_binary(data)}|acc])
  end
  def decode(<<1::size(1),0::size(1),tag::size(4),type::size(2),rest::binary>>,acc) do
    {data,rest} = packet_old(type,rest); decode(rest,[%{tag: tag, data: data}|acc])
  end
  def decode(_,acc), do: Enum.reverse(acc)

  def encode(packets), do: encode(packets,[])
  def encode([%{tag: tag, data: data}|rest],acc), do:
    encode(rest,[acc,<<1::size(1),0::size(1),tag::size(4),2::size(2),byte_size(data)::size(32),data::binary>>])
  def encode(_,acc), do: IO.iodata_to_binary(acc)

  def packet_old(0,<<l,data::binary-size(l),rest::binary>>), do: {data,rest}
  def packet_old(1,<<l::size(16),data::binary-size(l),rest::binary>>), do: {data,rest}
  def packet_old(2,<<l::size(32),data::binary-size(l),rest::binary>>), do: {data,rest}
  def packet_old(3,rest), do: {rest,""}

  def packet_new(<<0xFF,l::size(32),data::binary-size(l),rest::binary>>), do: {[data],rest}
  def packet_new(<<0b111::3,l::5,rest::binary>>) do
    l = 1 <<< l; <<data::binary-size(l),rest::binary>> = rest
    {next_data,rest} = packet_new(rest)
    {[data|next_data],rest}
  end
  def packet_new(<<0b11::2,l::14,rest::binary>>) do
    l = l + 0b1100_0000; <<data::binary-size(l),rest::binary>> = rest
    {[data],rest}
  end
  def packet_new(<<l,data::binary-size(l),rest::binary>>), do: {[data],rest}

  def fingerprint(%{data: d}), do: fingerprint(d)
  def fingerprint(d) when is_binary(d), do:
    :crypto.hash(:sha,<<0x99,byte_size(d)::size(16)>> <> d)

  def split_pub_priv(<<4,_date::32,algo,rest::binary>>=bin) do
    nb_mpi = if algo == 17, do: 4, else: 2
    rest = Enum.reduce(1..nb_mpi,rest,fn _,<<len::16,rest::binary>>-> bin_len = div(len+7,8)
      <<_::binary-size(bin_len),rest::binary>> = rest; rest
    end)
    {binary_part(bin,0,byte_size(bin)-byte_size(rest)),rest}
  end
end

defmodule Paperkey do
  import Bitwise
  def decode(<<0,keys::binary>>), do: decode(keys,%{})
  def decode(<<4,fingerprint::binary-size(20),l::size(16),key::binary-size(l),rest::binary>>,acc), do:
    decode(rest,Dict.put(acc,fingerprint,key))
  def decode(_,acc), do: acc

  def encode(keys) do
    [0|for {fingerprint,key}<-Enum.reverse(keys) do
      [4,fingerprint,<<byte_size(key)::size(16)>>,key]
    end] |> IO.iodata_to_binary
  end

  def get_paperkeys(priv_bin) do
    Pgp.decode(priv_bin) |> Enum.filter(& &1.tag in [5,7]) |> Enum.map(fn %{data: d}->
      {pub,priv} = Pgp.split_pub_priv(d)
      {Pgp.fingerprint(pub),priv}
    end) |> Enum.into(%{}) |> encode
  end

  [0x000000, 0x864cfb, 0x8ad50d, 0x0c99f6, 0x93e6e1, 0x15aa1a, 0x1933ec, 0x9f7f17, 0xa18139, 0x27cdc2, 0x2b5434, 0xad18cf, 0x3267d8, 0xb42b23, 0xb8b2d5, 0x3efe2e, 0xc54e89, 0x430272, 0x4f9b84, 0xc9d77f, 0x56a868, 0xd0e493, 0xdc7d65, 0x5a319e, 0x64cfb0, 0xe2834b, 0xee1abd, 0x685646, 0xf72951, 0x7165aa, 0x7dfc5c, 0xfbb0a7, 0x0cd1e9, 0x8a9d12, 0x8604e4, 0x00481f, 0x9f3708, 0x197bf3, 0x15e205, 0x93aefe, 0xad50d0, 0x2b1c2b, 0x2785dd, 0xa1c926, 0x3eb631, 0xb8faca, 0xb4633c, 0x322fc7, 0xc99f60, 0x4fd39b, 0x434a6d, 0xc50696, 0x5a7981, 0xdc357a, 0xd0ac8c, 0x56e077, 0x681e59, 0xee52a2, 0xe2cb54, 0x6487af, 0xfbf8b8, 0x7db443, 0x712db5, 0xf7614e, 0x19a3d2, 0x9fef29, 0x9376df, 0x153a24, 0x8a4533, 0x0c09c8, 0x00903e, 0x86dcc5, 0xb822eb, 0x3e6e10, 0x32f7e6, 0xb4bb1d, 0x2bc40a, 0xad88f1, 0xa11107, 0x275dfc, 0xdced5b, 0x5aa1a0, 0x563856, 0xd074ad, 0x4f0bba, 0xc94741, 0xc5deb7, 0x43924c, 0x7d6c62, 0xfb2099, 0xf7b96f, 0x71f594, 0xee8a83, 0x68c678, 0x645f8e, 0xe21375, 0x15723b, 0x933ec0, 0x9fa736, 0x19ebcd, 0x8694da, 0x00d821, 0x0c41d7, 0x8a0d2c, 0xb4f302, 0x32bff9, 0x3e260f, 0xb86af4, 0x2715e3, 0xa15918, 0xadc0ee, 0x2b8c15, 0xd03cb2, 0x567049, 0x5ae9bf, 0xdca544, 0x43da53, 0xc596a8, 0xc90f5e, 0x4f43a5, 0x71bd8b, 0xf7f170, 0xfb6886, 0x7d247d, 0xe25b6a, 0x641791, 0x688e67, 0xeec29c, 0x3347a4, 0xb50b5f, 0xb992a9, 0x3fde52, 0xa0a145, 0x26edbe, 0x2a7448, 0xac38b3, 0x92c69d, 0x148a66, 0x181390, 0x9e5f6b, 0x01207c, 0x876c87, 0x8bf571, 0x0db98a, 0xf6092d, 0x7045d6, 0x7cdc20, 0xfa90db, 0x65efcc, 0xe3a337, 0xef3ac1, 0x69763a, 0x578814, 0xd1c4ef, 0xdd5d19, 0x5b11e2, 0xc46ef5, 0x42220e, 0x4ebbf8, 0xc8f703, 0x3f964d, 0xb9dab6, 0xb54340, 0x330fbb, 0xac70ac, 0x2a3c57, 0x26a5a1, 0xa0e95a, 0x9e1774, 0x185b8f, 0x14c279, 0x928e82, 0x0df195, 0x8bbd6e, 0x872498, 0x016863, 0xfad8c4, 0x7c943f, 0x700dc9, 0xf64132, 0x693e25, 0xef72de, 0xe3eb28, 0x65a7d3, 0x5b59fd, 0xdd1506, 0xd18cf0, 0x57c00b, 0xc8bf1c, 0x4ef3e7, 0x426a11, 0xc426ea, 0x2ae476, 0xaca88d, 0xa0317b, 0x267d80, 0xb90297, 0x3f4e6c, 0x33d79a, 0xb59b61, 0x8b654f, 0x0d29b4, 0x01b042, 0x87fcb9, 0x1883ae, 0x9ecf55, 0x9256a3, 0x141a58, 0xefaaff, 0x69e604, 0x657ff2, 0xe33309, 0x7c4c1e, 0xfa00e5, 0xf69913, 0x70d5e8, 0x4e2bc6, 0xc8673d, 0xc4fecb, 0x42b230, 0xddcd27, 0x5b81dc, 0x57182a, 0xd154d1, 0x26359f, 0xa07964, 0xace092, 0x2aac69, 0xb5d37e, 0x339f85, 0x3f0673, 0xb94a88, 0x87b4a6, 0x01f85d, 0x0d61ab, 0x8b2d50, 0x145247, 0x921ebc, 0x9e874a, 0x18cbb1, 0xe37b16, 0x6537ed, 0x69ae1b, 0xefe2e0, 0x709df7, 0xf6d10c, 0xfa48fa, 0x7c0401, 0x42fa2f, 0xc4b6d4, 0xc82f22, 0x4e63d9, 0xd11cce, 0x575035, 0x5bc9c3, 0xdd8538]
  |> Enum.with_index |> Enum.map(fn {x,i}-> def crc24def(unquote(i)) do unquote(x) end end)
  def crc24(bin), do: crc24(bin,0xb704ce)
  def crc24(<<>>,crc), do: <<crc::size(24)>>
  def crc24(<<v>> <> rest,crc), do:
    crc24(rest,(crc <<< 8) ^^^ crc24def((crc >>> 16 ^^^ v) &&& 255))

  def put_paperkeys(paperkeys_bin,pub_file,out_file) do
    keys = decode(paperkeys_bin)
    res = File.read!(pub_file) |> Pgp.decode |> Enum.map(fn
      %{tag: tag, data: d}=packet when tag in [6,14]->
        fingerprint=Pgp.fingerprint(packet)
        case keys[fingerprint] do
          nil->packet
          k->IO.puts("Include private #{if tag==14, do: "sub"}key #{Base.encode16 fingerprint}")
             %{tag: if(tag==6, do: 5, else: 7), data: d<>k}
        end
      packet-> packet
    end) |> Pgp.encode
    File.write!(out_file,res)
  end

  @explanations """
# format: [v:1,(pgp_v:1,fingerpr:20,secret_len:2,secret:secret_len)*]
# a) 1 octet:  Version of the paperkey format (currently 0).
# b) 1 octet:  OpenPGP key or subkey version (currently 4)
# c) n octets: Key fingerprint (20 octets for a version 4 key or subkey)
# d) 2 octets: 16-bit big endian length of the following secret data
# e) n octets: Secret data: a partial OpenPGP secret key or subkey packet as
#              specified in RFC 4880, starting with the string-to-key usage
#              octet and continuing until the end of the packet.
# Repeat fields b through e as needed to cover all subkeys.
# 
# To recover the PGP secret cert:
# - take the PGP public cert, see rfc4880 for the packet format
# - split packets into [{tag,data}], we will replace public key packets (tag 6 or 14)
# - get priv key in paperkey from fingerprint: sha1(<<0x99,byte_size(d)::size(16),data::binary>>)
# - transform {tag = 6 or 14, data = pubdata} to {tag = 5 or 7, data = pubdata <> key}
# - encode and join packets
#
  """

  def format_bin(bin), do: (bin <> crc24(bin))
  def extract_bin(bin) do
    content = binary_part(bin,0,byte_size(bin)-3)
    if crc24(content) != binary_part(bin,byte_size(bin),-3), do: 
      throw("Invalid CRC ! Corrupted data")
    content
  end

  def format_hexa(bin) do
    lines = :erlang.binary_to_list(bin)
     |> Enum.chunk(22,22,[]) |> Enum.with_index |> Enum.map(fn {bytes,i}->
       String.rjust(to_string(i+1),5) <> ": " <>
       (bytes |> Enum.map(&Base.encode16(<<&1>>)) |> Enum.join(" ")) <> " " <>
       (bytes |> IO.iodata_to_binary |> crc24 |> Base.encode16)
     end)
    crc = String.rjust(to_string(length(lines)+1),5) <> ": " <> Base.encode16(crc24(bin))
    "#{@explanations}\n#crc24 at eol for each line and last line is the entire crc24\n\n"<>
    "#{Enum.join(lines,"\n")}\n#{crc}"
  end
  def extract_hexa(hexa_str) do
    res = Regex.scan(~r/^\s*([0-9]+): (.*) ([A-F0-9]{6})$/m,hexa_str)
     |> Enum.map(fn [_,line,hexa,crc]->
       bin = hexa |> String.replace(" ","") |> Base.decode16!
       if crc24(bin) != Base.decode16!(crc), do: throw("Line #{line}, CRC fail"), else: bin
     end)
     |> Enum.into(<<>>)
    [_,crc] = Regex.run(~r/^\s*[0-9]+: ([A-F0-9]{6})$/m,hexa_str)
    if crc24(res) != Base.decode16!(crc), do:
      throw("Invalid global CRC ! Corrupted data")
    res
  end

  def format_base64(bin) do
    "#{@explanations}\n#===== base64 binary encoded: last 3 bytes are crc24 ====:\n\n"<>
    "#{bin |> format_bin |> Base.encode64 |> to_char_list |> Enum.chunk(80,80,[]) |> Enum.intersperse(?\n)}"
  end
  def extract_base64(str) do
    str |> String.split(~r"====:\n") |> List.last |> String.replace(~r"\s","") 
        |> Base.decode64! |> extract_bin
  end
end

case System.argv do
  ["import","binary",pgp_in,pgp_out]->
    IO.read(:stdio,:all) |> Paperkey.extract_bin |> Paperkey.put_paperkeys(pgp_in,pgp_out)
  ["import","base64",pgp_in,pgp_out]->
    IO.read(:stdio,:all) |> Paperkey.extract_base64 |>  Paperkey.put_paperkeys(pgp_in,pgp_out)
  ["import","hexa",pgp_in,pgp_out]->
    IO.read(:stdio,:all) |> Paperkey.extract_hexa |> Paperkey.put_paperkeys(pgp_in,pgp_out)
  ["export","binary"]->
    IO.read(:stdio,:all) |> Paperkey.get_paperkeys |> Paperkey.format_bin |> IO.write
  ["export","base64"]->
    IO.read(:stdio,:all) |> Paperkey.get_paperkeys |> Paperkey.format_base64 |> IO.write
  ["export","hexa"]->
    IO.read(:stdio,:all) |> Paperkey.get_paperkeys |> Paperkey.format_hexa |> IO.write
  _ -> 
    IO.puts """
    usage : 
      elixir paperkey.exs import (binary|hexa|base64) pub_pgp_file out_pgp_file"
      elixir paperkey.exs export (binary|hexa|base64)"
    Include PGP Paperkey private keys into a given PGP file. 
    
    When "import", Paperkey private keys are read from stdin, stdout shows included keys fingerprint
    When "export", Gpg private file are read from stdin, paperkey binary is output on stdout

    Format of the input (for import) and output (for export) can be:
    - "binary" : raw (binary) paperkey format
    - "hexa" : default text paperkey format (hexa with crc24)
    - "base64" : base64 encoded binary paperkey
    """
end
