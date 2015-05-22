#!/bin/bash

function delall 
{
  find -name "$1" -print
  find -name "$1" -delete
}

delall '*.agdai'
delall log
