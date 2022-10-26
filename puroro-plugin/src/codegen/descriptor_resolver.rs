// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::restructure::{Enum, File, Message, MessageOrEnumRef};
use super::utils::{Fqtn, PackageName};
use crate::{ErrorKind, Result};
use ::itertools::Itertools;
use ::std::collections::{HashMap, HashSet};
use ::std::fmt::Debug;

#[derive(Debug)]
pub struct DescriptorResolver<'a> {
    fqtn_to_desc_map: HashMap<Fqtn, MessageOrEnumRef<'a>>,
    package_contents: HashMap<PackageName<String>, PackageContents<'a>>,
}
impl<'a> DescriptorResolver<'a> {
    pub fn new<I>(input_files: I) -> Result<Self>
    where
        I: IntoIterator<Item = &'a File<'a>>,
    {
        let mut fqtn_to_desc_map = HashMap::new();
        let mut package_contents_vec = Vec::new();
        for f in input_files {
            Self::generate_fqtn_to_desc_map(&mut fqtn_to_desc_map, f);
            package_contents_vec.extend(Self::generate_package_contents(f));
        }
        let mut package_contents = HashMap::<_, PackageContents>::new();
        for pc in package_contents_vec {
            if let Some(existing_pc) = package_contents.get_mut(&pc.full_package) {
                existing_pc.merge(pc)?;
            } else {
                package_contents.insert(pc.full_package.clone(), pc);
            }
        }

        Ok(Self {
            fqtn_to_desc_map,
            package_contents,
        })
    }

    fn generate_fqtn_to_desc_map(
        fqtn_to_desc_map: &mut HashMap<Fqtn, MessageOrEnumRef<'a>>,
        file: &'a File<'a>,
    ) {
        for &m in file.all_messages() {
            fqtn_to_desc_map.insert(m.fqtn().to_owned(), MessageOrEnumRef::Message(m));
        }
        for &e in file.all_enums() {
            fqtn_to_desc_map.insert(e.fqtn().to_owned(), MessageOrEnumRef::Enum(e));
        }
    }

    fn generate_package_contents(
        file: &'a File<'a>,
    ) -> impl 'a + IntoIterator<Item = PackageContents<'a>> {
        // package_contents for parent packages
        let mut branches = file
            .package()
            .packages_and_subpackages()
            .map(|(cur_package, subpackage)| PackageContents {
                package_name: cur_package.leaf_package_name().map(|s| s.to_string()),
                full_package: cur_package.to_owned(),
                subpackages: HashSet::from_iter([subpackage.to_string()].into_iter()),
                input_files: Vec::new(),
            })
            .collect_vec();

        // package_contents for the leaf package
        let term_item = PackageContents {
            package_name: file.package().leaf_package_name().map(|s| s.to_string()),
            full_package: file.package().to_owned(),
            input_files: vec![File::new(file)],
            subpackages: HashSet::new(),
        };

        branches.push(term_item);
        branches
    }

    pub fn fqtn_to_desc(&self, fqtn: &Fqtn) -> Option<MessageOrEnumRef<'a>> {
        self.fqtn_to_desc_map.get(fqtn).cloned()
    }

    pub fn fqtn_to_desc_or_err(&self, fqtn: &Fqtn) -> Result<MessageOrEnumRef<'a>> {
        Ok(self.fqtn_to_desc(fqtn).ok_or(ErrorKind::UnknownTypeName {
            name: format!("{:?}", fqtn),
        })?)
    }

    pub fn fqtn_to_message(&self, fqtn: &Fqtn) -> Result<&'a Message<'a>> {
        match self.fqtn_to_desc_or_err(fqtn)? {
            MessageOrEnumRef::Message(m) => Ok(m),
            MessageOrEnumRef::Enum(_) => Err(ErrorKind::UnknownTypeName {
                name: format!("Message {:?}", fqtn),
            })?,
        }
    }

    pub fn fqtn_to_enum(&self, fqtn: &Fqtn) -> Result<&'a Enum<'a>> {
        match self.fqtn_to_desc_or_err(fqtn)? {
            MessageOrEnumRef::Enum(e) => Ok(e),
            MessageOrEnumRef::Message(_) => Err(ErrorKind::UnknownTypeName {
                name: format!("Enum {:?}", fqtn),
            })?,
        }
    }

    pub fn package_contents<S: AsRef<str>>(
        &self,
        package: &PackageName<S>,
    ) -> Option<&PackageContents<'a>> {
        self.package_contents.get::<str>(package.as_str())
    }

    pub fn package_contents_or_err<S: AsRef<str>>(
        &self,
        package: &PackageName<S>,
    ) -> Result<&PackageContents<'a>> {
        Ok(self
            .package_contents(package)
            .ok_or(ErrorKind::UnknownTypeName {
                name: package.as_str().into(),
            })?)
    }

    #[allow(unused)]
    pub fn all_packages(&'a self) -> impl Iterator<Item = &PackageContents<'a>> {
        self.package_contents.values()
    }
}

#[derive(Debug, Default)]
pub struct PackageContents<'a> {
    pub package_name: Option<String>,
    pub full_package: PackageName<String>,
    pub subpackages: HashSet<String>,
    pub input_files: Vec<File<'a>>,
}

impl PackageContents<'_> {
    fn merge(&mut self, mut rhs: Self) -> Result<()> {
        if self.package_name != rhs.package_name || self.full_package != rhs.full_package {
            Err(ErrorKind::InternalError {
                detail: "Tried to merge different name PackageContents".to_string(),
            })?
        }
        self.subpackages.extend(rhs.subpackages.drain());
        self.input_files.append(&mut rhs.input_files);
        Ok(())
    }
}
