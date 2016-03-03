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
# > gpg --export-secret-key A81C573A | elixir paperkey.exs export binary | openssl enc -base64 | split -b 669 - key-
# > for K in key-*; do; cat $K | qrencode -S -v 22 -l L -o $K.png ; done
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

  def crc24(bin), do: crc24(bin,<<0xb704ce::24>>)
  def crc24(<<>>,crc), do: crc
  def crc24(<<v>> <> rest,<<crc0,crc1,crc2>>) do
    crc = 1..8 |> Enum.reduce(<<v ^^^ crc0,crc1,crc2>>,fn _,crc->
      case <<crc::binary-size(24)-unit(1),0::size(1)>> do
        <<0::size(1),crc::binary-size(24)-unit(1)>>-> crc
        <<num_crc::size(25)>> -> <<num_crc ^^^ 0x864cfb::size(24)>>
      end
    end)
    crc24(rest,crc)
  end

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
