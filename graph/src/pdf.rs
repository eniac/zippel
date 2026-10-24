//! Rendering graphs to PDF through Graphviz.

use super::*;
use petgraph::dot::Dot;
use std::path::PathBuf;
use std::process::Command;

/// Write graphs with string annotations to PDF
impl<C: Backend> WritePdf for Dag<C, String> {
    /// Write graph to PDF
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        let fdot: String = format!("{filename}.dot");
        // Remove old file if there
        std::fs::remove_file(&fdot).ok();

        // Create graphviz object
        let graphviz = Dot::with_attr_getters(
            &self.graph,
            &[],
            &|_, e| {
                match e.weight().0 {
                    DepType::Data => "color = \"black\"",
                    DepType::Transcript => "color = \"red\"",
                }
                .to_string()
            },
            &|_, n| match n.1 {
                Node::Inp(_) => "shape = \"box\"".to_string(),
                Node::Rel(_) => "shape = \"note\"".to_string(),
                Node::Arg(_, _, _, _, _) => "shape = \"parallelogram\"".to_string(),
                Node::Transcr(_, _) => "color = \"red\"".to_string(),
                _ => "shape = \"ellipse\"".to_string(),
            },
        );

        // Write to file
        std::fs::write(fdot.clone(), graphviz.to_string())?;

        let fpdf: String = format!("{filename}.pdf");

        // Convert to pdf
        Command::new("dot")
            .arg("-Tpdf")
            .arg(fdot.clone())
            .arg("-o")
            .arg(fpdf.clone())
            .spawn()?
            .wait()?;

        // Remove DOT file
        // std::fs::remove_file(fdot)?;

        debug!("Wrote PDF to {:?}", fpdf);
        // Print success
        debug!(
            "Wrote {:?}",
            std::fs::canonicalize(PathBuf::from(fpdf.clone()))
        );
        Ok(())
    }
}

impl<C: Backend> WritePdf for UDag<C> {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        self.map_annotations(&|_, _| "".to_string())
            .write_pdf(filename)
    }
}

impl<C: Backend> WritePdf for QDag<C> {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        self.map_annotations(&|_, q| q.to_string())
            .write_pdf(filename)
    }
}

impl<C: Backend> WritePdf for Dags<C, String> {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        let mut joined_graph = Dag::new();
        for g in self.0.iter() {
            joined_graph = joined_graph.combine_dag(g);
        }
        joined_graph.write_pdf(filename)
    }
}

impl<C: Backend> WritePdf for UDags<C> {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        self.map_annotations(&|_, _| "".to_string())
            .write_pdf(filename)
    }
}

impl<C: Backend> WritePdf for QDags<C> {
    fn write_pdf(&self, filename: &str) -> std::io::Result<()> {
        self.map_annotations(&|_, q| q.to_string())
            .write_pdf(filename)
    }
}
